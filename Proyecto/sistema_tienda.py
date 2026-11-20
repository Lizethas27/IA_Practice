#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
==============================================================================
 SIGECO - Sistema Integral de Gestión Comercial
 Cadena "Abarrotes del Bajío"
==============================================================================

Módulo monolítico heredado (legacy) que concentra la lógica de:

  * utilerías de texto, fechas, números y finanzas
  * estructuras de datos de uso general (caché LRU, trie, union-find, ...)
  * catálogo de entidades del negocio (proveedores, productos, sucursales, ...)
  * inventario, precios, ventas, facturación y nómina
  * grafos para el cálculo de rutas de reparto
  * un pequeño evaluador de fórmulas para listas de precios
  * reportes en texto y una batería de pruebas internas

Uso:
    python sistema_tienda.py              # ejecuta todas las pruebas internas
    python sistema_tienda.py -v           # ejecuta las pruebas mostrando también las que pasan
    python sistema_tienda.py -k kardex    # ejecuta solo las pruebas cuyo nombre contenga "kardex"
    python sistema_tienda.py --lista      # lista las pruebas disponibles
    python sistema_tienda.py --demo       # ejecuta una simulación de un día de ventas

Solo depende de la biblioteca estándar de Python (3.9+).
"""
from __future__ import annotations

import bisect
import copy
import csv
import functools
import hashlib
import heapq
import io
import itertools
import json
import math
import random
import re
import sys
import textwrap
import traceback
import unicodedata
from collections import Counter, OrderedDict, defaultdict, deque
from dataclasses import asdict, dataclass, field, fields, replace
from datetime import date, datetime, timedelta
from decimal import ROUND_HALF_EVEN, ROUND_HALF_UP, Decimal
from typing import Any, Callable, Dict, Iterable, Iterator, List, Optional, Sequence, Tuple


# ==============================================================================
# SECCIÓN 1. CONFIGURACIÓN GENERAL
# ==============================================================================

VERSION = "4.12.3"
NOMBRE_EMPRESA = "Abarrotes del Bajío S.A. de C.V."
RFC_EMPRESA = "ABA950315KT2"
MONEDA = "MXN"

TASA_IVA = 0.16
TASA_IEPS_BEBIDAS = 0.08
TASA_RETENCION_ISR = 0.0125
FACTOR_RETENCION_IVA = 2 / 3

SALARIO_MINIMO_DIARIO = 278.80
UMA_DIARIA = 113.14
DIAS_MES_NOMINA = 30.4
SUBSIDIO_EMPLEO_LIMITE = 10171.00
SUBSIDIO_EMPLEO_MONTO = 475.00

DENOMINACIONES_MXN = (1000, 500, 200, 100, 50, 20, 10, 5, 2, 1, 0.5)

FORMATOS_FECHA = ("%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%Y%m%d", "%d.%m.%Y")

LETRAS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
DIGITOS = "0123456789"

CONFIGURACION_POR_DEFECTO: Dict[str, Any] = {
    "sucursal_matriz": "SUC001",
    "dias_credito_default": 30,
    "existencia_minima_default": 5,
    "redondeo_efectivo": 0.5,
    "max_lineas_ticket": 200,
    "mostrar_ieps_desglosado": True,
    "capacidad_cache_precios": 256,
    "zona_horaria": "America/Mexico_City",
    "ticket": {
        "ancho": 42,
        "mostrar_rfc": True,
        "leyenda": "GRACIAS POR SU COMPRA",
    },
}


# ==============================================================================
# SECCIÓN 2. EXCEPCIONES DEL DOMINIO
# ==============================================================================


class ErrorSistema(Exception):
    """Excepción base de todo el sistema."""


class ErrorValidacion(ErrorSistema):
    """Se lanza cuando una entidad no cumple sus reglas de validación."""

    def __init__(self, entidad: str, errores: Iterable[str]):
        self.entidad = entidad
        self.errores = list(errores)
        super().__init__(f"{entidad}: " + "; ".join(self.errores))


class EntidadNoEncontrada(ErrorSistema):
    """Se lanza al buscar un registro inexistente."""


class StockInsuficiente(ErrorSistema):
    """Se lanza cuando no hay existencias suficientes para surtir una salida."""

    def __init__(self, sku: str, solicitado: int, disponible: int):
        self.sku = sku
        self.solicitado = solicitado
        self.disponible = disponible
        super().__init__(
            f"Stock insuficiente para {sku}: solicitado={solicitado}, disponible={disponible}"
        )


class ErrorParser(ErrorSistema):
    """Errores del evaluador de fórmulas."""


class ErrorRuta(ErrorSistema):
    """Errores en el cálculo de rutas de reparto."""


class ErrorConfiguracion(ErrorSistema):
    """Errores de configuración."""


# ==============================================================================
# SECCIÓN 3. CONFIGURACIÓN EN TIEMPO DE EJECUCIÓN
# ==============================================================================


def fusionar_diccionarios(base: Dict[str, Any], cambios: Dict[str, Any]) -> Dict[str, Any]:
    """Fusiona recursivamente ``cambios`` sobre una copia de ``base``."""
    resultado = dict(base)
    for clave, valor in cambios.items():
        if isinstance(valor, dict) and isinstance(resultado.get(clave), dict):
            resultado[clave] = fusionar_diccionarios(resultado[clave], valor)
        else:
            resultado[clave] = valor
    return resultado


class Configuracion:
    """Contenedor de configuración con acceso por rutas tipo ``seccion.clave``."""

    def __init__(self, valores: Optional[Dict[str, Any]] = None):
        base = copy.deepcopy(CONFIGURACION_POR_DEFECTO)
        self._valores = fusionar_diccionarios(base, valores or {})

    def obtener(self, ruta: str, por_defecto: Any = None) -> Any:
        actual: Any = self._valores
        for parte in ruta.split("."):
            if not isinstance(actual, dict) or parte not in actual:
                return por_defecto
            actual = actual[parte]
        return actual

    def establecer(self, ruta: str, valor: Any) -> None:
        partes = ruta.split(".")
        actual = self._valores
        for parte in partes[:-1]:
            siguiente = actual.get(parte)
            if siguiente is None:
                siguiente = {}
                actual[parte] = siguiente
            elif not isinstance(siguiente, dict):
                raise ErrorConfiguracion(f"'{parte}' no es una sección en la ruta {ruta}")
            actual = siguiente
        actual[partes[-1]] = valor

    def como_dict(self) -> Dict[str, Any]:
        return json.loads(json.dumps(self._valores))

    def validar(self) -> List[str]:
        errores: List[str] = []
        if not isinstance(self.obtener("dias_credito_default"), int):
            errores.append("dias_credito_default debe ser entero")
        if self.obtener("capacidad_cache_precios", 0) <= 0:
            errores.append("capacidad_cache_precios debe ser positiva")
        if self.obtener("redondeo_efectivo") not in (0.01, 0.1, 0.5, 1):
            errores.append("redondeo_efectivo debe ser 0.01, 0.1, 0.5 o 1")
        ancho = self.obtener("ticket.ancho", 0)
        if not isinstance(ancho, int) or not 32 <= ancho <= 80:
            errores.append("ticket.ancho debe estar entre 32 y 80")
        return errores


# ==============================================================================
# SECCIÓN 4. UTILERÍAS DE TEXTO
# ==============================================================================

PARTICULAS_NOMBRE = {"de", "del", "la", "las", "los", "y", "e", "van", "von"}


def quitar_acentos(texto: str) -> str:
    """Elimina acentos y diacríticos (á -> a, ñ -> n, ü -> u)."""
    normalizado = unicodedata.normalize("NFKD", texto)
    return "".join(c for c in normalizado if not unicodedata.combining(c))


def normalizar_espacios(texto: str) -> str:
    """Colapsa espacios múltiples y recorta extremos."""
    return " ".join(texto.split())


def slugify(texto: str) -> str:
    """Convierte un texto en un identificador apto para URLs."""
    texto = quitar_acentos(texto).lower()
    texto = re.sub(r"[^a-z0-9]+", "-", texto)
    return texto.strip("-")


def capitalizar_nombre(nombre: str) -> str:
    """Capitaliza un nombre propio respetando partículas (de, del, la, ...)."""
    palabras = normalizar_espacios(nombre).lower().split(" ")
    resultado = []
    for indice, palabra in enumerate(palabras):
        if indice > 0 and palabra in PARTICULAS_NOMBRE:
            resultado.append(palabra)
        else:
            resultado.append(palabra[:1].upper() + palabra[1:])
    return " ".join(resultado)


def truncar(texto: str, longitud: int, sufijo: str = "...") -> str:
    """Recorta ``texto`` a ``longitud`` caracteres incluyendo el sufijo."""
    if len(texto) <= longitud:
        return texto
    if longitud <= len(sufijo):
        return sufijo[:longitud]
    return texto[: longitud - len(sufijo)].rstrip() + sufijo


def enmascarar(texto: str, visibles: int = 4, caracter: str = "*") -> str:
    """Enmascara todo excepto los últimos ``visibles`` caracteres."""
    if visibles <= 0:
        return caracter * len(texto)
    if len(texto) <= visibles:
        return texto
    return caracter * (len(texto) - visibles) + texto[-visibles:]


def contar_palabras(texto: str) -> Dict[str, int]:
    """Frecuencia de palabras (sin acentos y en minúsculas)."""
    palabras = re.findall(r"[a-z0-9ñ]+", quitar_acentos(texto.lower()))
    return dict(Counter(palabras))


def extraer_numeros(texto: str) -> List[float]:
    """Extrae todos los números (enteros o decimales) presentes en un texto."""
    return [float(n.replace(",", "")) for n in re.findall(r"-?\d[\d,]*(?:\.\d+)?", texto)]


def es_palindromo(texto: str) -> bool:
    limpio = re.sub(r"[^a-z0-9]", "", quitar_acentos(texto.lower()))
    return limpio == limpio[::-1]


def rellenar_plantilla(plantilla: str, **valores: Any) -> str:
    """Sustituye marcadores ``{{nombre}}`` por los valores dados."""

    def sustituir(coincidencia: "re.Match[str]") -> str:
        clave = coincidencia.group(1).strip()
        if clave not in valores:
            raise KeyError(f"falta el valor para el marcador '{clave}'")
        return str(valores[clave])

    return re.sub(r"\{\{\s*([A-Za-z_][A-Za-z0-9_]*)\s*\}\}", sustituir, plantilla)


_PATRON_EMAIL = re.compile(r"^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}$")
_PATRON_RFC = re.compile(r"^([A-ZÑ&]{3,4})(\d{2})(\d{2})(\d{2})([A-Z0-9]{3})$")
_PATRON_FECHA_ISO = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def es_email_valido(correo: str) -> bool:
    return isinstance(correo, str) and bool(_PATRON_EMAIL.match(correo.strip()))


def es_rfc_valido(rfc: str) -> bool:
    """Valida la estructura de un RFC mexicano (persona física o moral)."""
    if not isinstance(rfc, str):
        return False
    coincidencia = _PATRON_RFC.match(rfc.strip().upper())
    if not coincidencia:
        return False
    mes, dia = int(coincidencia.group(3)), int(coincidencia.group(4))
    return 1 <= mes <= 12 and 1 <= dia <= 31


def tipo_persona_por_rfc(rfc: str) -> str:
    """Los RFC de 12 caracteres pertenecen a personas morales."""
    return "persona_moral" if len(rfc.strip()) == 12 else "persona_fisica"


def normalizar_telefono(telefono: str) -> str:
    digitos = re.sub(r"\D", "", telefono or "")
    if digitos.startswith("52") and len(digitos) == 12:
        digitos = digitos[2:]
    return digitos


def es_telefono_valido(telefono: str) -> bool:
    return isinstance(telefono, str) and len(normalizar_telefono(telefono)) == 10


def es_fecha_iso(texto: str) -> bool:
    if not isinstance(texto, str) or not _PATRON_FECHA_ISO.match(texto):
        return False
    try:
        date.fromisoformat(texto)
    except ValueError:
        return False
    return True


def a_booleano(valor: Any) -> bool:
    """Interpreta valores comunes ("sí", "1", "true", ...) como booleanos."""
    if isinstance(valor, bool):
        return valor
    if isinstance(valor, (int, float)):
        return valor != 0
    texto = str(valor).strip().lower()
    if texto in ("true", "1", "si", "sí", "s", "yes", "y", "verdadero"):
        return True
    if texto in ("false", "0", "no", "n", "falso", ""):
        return False
    raise ValueError(f"no se puede interpretar como booleano: {valor!r}")


def formatear_moneda(monto: float, simbolo: str = "$") -> str:
    signo = "-" if monto < 0 else ""
    return f"{signo}{simbolo}{abs(monto):,.2f}"


def formatear_porcentaje(valor: float, decimales: int = 1) -> str:
    return f"{valor:.{decimales}f}%"


_UNIDADES = [
    "", "UNO", "DOS", "TRES", "CUATRO", "CINCO", "SEIS", "SIETE", "OCHO", "NUEVE",
    "DIEZ", "ONCE", "DOCE", "TRECE", "CATORCE", "QUINCE", "DIECISÉIS", "DIECISIETE",
    "DIECIOCHO", "DIECINUEVE", "VEINTE", "VEINTIUNO", "VEINTIDÓS", "VEINTITRÉS",
    "VEINTICUATRO", "VEINTICINCO", "VEINTISÉIS", "VEINTISIETE", "VEINTIOCHO", "VEINTINUEVE",
]
_DECENAS = ["", "", "", "TREINTA", "CUARENTA", "CINCUENTA", "SESENTA", "SETENTA", "OCHENTA", "NOVENTA"]
_CENTENAS = [
    "", "CIENTO", "DOSCIENTOS", "TRESCIENTOS", "CUATROCIENTOS", "QUINIENTOS",
    "SEISCIENTOS", "SETECIENTOS", "OCHOCIENTOS", "NOVECIENTOS",
]


def _convertir_menor_mil(numero: int) -> str:
    if numero == 0:
        return ""
    if numero == 100:
        return "CIEN"
    centenas, resto = divmod(numero, 100)
    partes = []
    if centenas:
        partes.append(_CENTENAS[centenas])
    if resto:
        if resto < 30:
            partes.append(_UNIDADES[resto])
        else:
            decenas, unidades = divmod(resto, 10)
            partes.append(_DECENAS[decenas] + (f" Y {_UNIDADES[unidades]}" if unidades else ""))
    return " ".join(partes)


def _apocopar(texto: str) -> str:
    """'VEINTIUNO MIL' -> 'VEINTIÚN MIL', 'TREINTA Y UNO' -> 'TREINTA Y UN'."""
    if texto.endswith("VEINTIUNO"):
        return texto[: -len("VEINTIUNO")] + "VEINTIÚN"
    if texto.endswith("UNO"):
        return texto[:-3] + "UN"
    return texto


def entero_a_letras(numero: int) -> str:
    """Convierte un entero a su representación en letras (español de México)."""
    if numero == 0:
        return "CERO"
    if numero < 0:
        return "MENOS " + entero_a_letras(-numero)
    partes = []
    millones, resto = divmod(numero, 1_000_000)
    miles, unidades = divmod(resto, 1000)
    if millones:
        if millones == 1:
            partes.append("UN MILLÓN")
        else:
            partes.append(_apocopar(entero_a_letras(millones)) + " MILLONES")
    if miles:
        if miles == 1:
            partes.append("MIL")
        else:
            partes.append(_apocopar(_convertir_menor_mil(miles)) + " MIL")
    if unidades:
        partes.append(_convertir_menor_mil(unidades))
    return " ".join(partes)


def monto_a_letras(monto: float, moneda_plural: str = "PESOS", moneda_singular: str = "PESO") -> str:
    """Importe con letra como se imprime en facturas: 'CIEN PESOS 00/100 M.N.'"""
    centavos_totales = int(round(abs(monto) * 100))
    enteros, centavos = divmod(centavos_totales, 100)
    if enteros == 1:
        texto = f"UN {moneda_singular}"
    else:
        texto = _apocopar(entero_a_letras(enteros))
        if enteros >= 1_000_000 and enteros % 1_000_000 == 0:
            texto += " DE"
        texto += f" {moneda_plural}"
    if monto < 0:
        texto = "MENOS " + texto
    return f"{texto} {centavos:02d}/100 M.N."


def levenshtein(a: str, b: str) -> int:
    """Distancia de edición entre dos cadenas."""
    if len(a) < len(b):
        a, b = b, a
    anterior = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        actual = [i]
        for j, cb in enumerate(b, start=1):
            costo = 0 if ca == cb else 1
            actual.append(min(anterior[j] + 1, actual[j - 1] + 1, anterior[j - 1] + costo))
        anterior = actual
    return anterior[-1]


def similitud(a: str, b: str) -> float:
    """Similitud normalizada en [0, 1] basada en Levenshtein."""
    a = quitar_acentos(a.lower())
    b = quitar_acentos(b.lower())
    if not a and not b:
        return 1.0
    return 1 - levenshtein(a, b) / max(len(a), len(b))


def sugerir_coincidencias(termino: str, opciones: Iterable[str], minimo: float = 0.6, limite: int = 3) -> List[str]:
    """Regresa las opciones más parecidas a ``termino`` (útil para búsquedas con errores de dedo)."""
    puntuadas = [(similitud(termino, o), o) for o in opciones]
    puntuadas = [p for p in puntuadas if p[0] >= minimo]
    puntuadas.sort(key=lambda p: (-p[0], p[1]))
    return [o for _, o in puntuadas[:limite]]


def digito_verificador_ean13(doce_digitos: str) -> int:
    if len(doce_digitos) != 12 or not doce_digitos.isdigit():
        raise ValueError("se requieren exactamente 12 dígitos")
    suma = sum(int(d) * (3 if i % 2 else 1) for i, d in enumerate(doce_digitos))
    return (10 - suma % 10) % 10


def validar_ean13(codigo: str) -> bool:
    if not isinstance(codigo, str) or len(codigo) != 13 or not codigo.isdigit():
        return False
    return digito_verificador_ean13(codigo[:12]) == int(codigo[12])


def validar_luhn(numero: str) -> bool:
    """Algoritmo de Luhn para números de tarjeta."""
    digitos = [int(c) for c in str(numero) if c.isdigit()]
    if len(digitos) < 2:
        return False
    total = 0
    for indice, digito in enumerate(reversed(digitos)):
        if indice % 2 == 1:
            digito *= 2
            if digito > 9:
                digito -= 9
        total += digito
    return total % 10 == 0


# ==============================================================================
# SECCIÓN 5. UTILERÍAS DE FECHAS
# ==============================================================================

_DIAS_POR_MES = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
NOMBRES_MES = [
    "enero", "febrero", "marzo", "abril", "mayo", "junio",
    "julio", "agosto", "septiembre", "octubre", "noviembre", "diciembre",
]
NOMBRES_DIA = ["lunes", "martes", "miércoles", "jueves", "viernes", "sábado", "domingo"]


def es_bisiesto(anio: int) -> bool:
    """Regla gregoriana: divisible entre 4, excepto los centenarios no divisibles entre 400."""
    return anio % 4 == 0 and anio % 100 != 0


def dias_en_mes(anio: int, mes: int) -> int:
    if not 1 <= mes <= 12:
        raise ValueError(f"mes inválido: {mes}")
    if mes == 2 and es_bisiesto(anio):
        return 29
    return _DIAS_POR_MES[mes - 1]


def dias_en_anio(anio: int) -> int:
    return 366 if es_bisiesto(anio) else 365


def sumar_meses(fecha: date, meses: int) -> date:
    """Suma meses calendario ajustando el día al último día válido del mes destino."""
    total = fecha.month - 1 + meses
    anio = fecha.year + total // 12
    mes = total % 12 + 1
    dia = min(fecha.day, dias_en_mes(anio, mes))
    return date(anio, mes, dia)


def fin_de_mes(fecha: date) -> date:
    return date(fecha.year, fecha.month, dias_en_mes(fecha.year, fecha.month))


def n_esimo_dia_semana(anio: int, mes: int, dia_semana: int, n: int) -> date:
    """n-ésimo día de la semana (0=lunes) de un mes."""
    primero = date(anio, mes, 1)
    desplazamiento = (dia_semana - primero.weekday()) % 7
    return primero + timedelta(days=desplazamiento + 7 * (n - 1))


def festivos_del_anio(anio: int) -> set:
    """Días de descanso obligatorio (Ley Federal del Trabajo, simplificado)."""
    fijos = {date(anio, 1, 1), date(anio, 5, 1), date(anio, 9, 16), date(anio, 12, 25)}
    moviles = {
        n_esimo_dia_semana(anio, 2, 0, 1),   # primer lunes de febrero
        n_esimo_dia_semana(anio, 3, 0, 3),   # tercer lunes de marzo
        n_esimo_dia_semana(anio, 11, 0, 3),  # tercer lunes de noviembre
    }
    return fijos | moviles


def es_dia_habil(fecha: date) -> bool:
    return fecha.weekday() < 5 and fecha not in festivos_del_anio(fecha.year)


def sumar_dias_habiles(fecha: date, dias: int) -> date:
    paso = 1 if dias >= 0 else -1
    restantes = abs(dias)
    actual = fecha
    while restantes > 0:
        actual += timedelta(days=paso)
        if es_dia_habil(actual):
            restantes -= 1
    return actual


def dias_habiles_entre(inicio: date, fin: date) -> int:
    """Días hábiles en el intervalo (inicio, fin]."""
    if fin < inicio:
        return -dias_habiles_entre(fin, inicio)
    cuenta = 0
    actual = inicio
    while actual < fin:
        actual += timedelta(days=1)
        if es_dia_habil(actual):
            cuenta += 1
    return cuenta


def trimestre(fecha: date) -> int:
    return (fecha.month - 1) // 3 + 1


def semana_iso(fecha: date) -> int:
    return fecha.isocalendar()[1]


def parsear_fecha(texto: str) -> date:
    texto = texto.strip()
    for formato in FORMATOS_FECHA:
        try:
            return datetime.strptime(texto, formato).date()
        except ValueError:
            continue
    raise ValueError(f"formato de fecha no reconocido: {texto!r}")


def fecha_larga(fecha: date) -> str:
    """'sábado 14 de marzo de 2026'"""
    return f"{NOMBRES_DIA[fecha.weekday()]} {fecha.day} de {NOMBRES_MES[fecha.month - 1]} de {fecha.year}"


def edad(fecha_nacimiento: date, hoy: Optional[date] = None) -> int:
    hoy = hoy or date.today()
    return hoy.year - fecha_nacimiento.year - ((hoy.month, hoy.day) < (fecha_nacimiento.month, fecha_nacimiento.day))


def rango_fechas(inicio: date, fin: date, paso_dias: int = 1) -> Iterator[date]:
    actual = inicio
    while actual <= fin:
        yield actual
        actual += timedelta(days=paso_dias)


def sumar_dias_iso(fecha_iso: str, dias: int) -> str:
    return (date.fromisoformat(fecha_iso) + timedelta(days=dias)).isoformat()


# ==============================================================================
# SECCIÓN 6. UTILERÍAS NUMÉRICAS Y ESTADÍSTICAS
# ==============================================================================


def redondear_bancario(valor: float, decimales: int = 2) -> float:
    cuanto = Decimal(1).scaleb(-decimales)
    return float(Decimal(str(valor)).quantize(cuanto, rounding=ROUND_HALF_EVEN))


def redondear_moneda(valor: float) -> float:
    """Redondeo comercial a centavos (mitad hacia arriba)."""
    return float(Decimal(str(valor)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))


def redondear_a_multiplo(valor: float, multiplo: float = 0.5) -> float:
    if multiplo <= 0:
        raise ValueError("el múltiplo debe ser positivo")
    return round(round(valor / multiplo) * multiplo, 2)


def limitar(valor: float, minimo: float, maximo: float) -> float:
    return max(minimo, min(maximo, valor))


def promedio(valores: Iterable[float]) -> float:
    """Media aritmética."""
    valores = list(valores)
    if not valores:
        raise ValueError("no se puede calcular el promedio de una secuencia vacía")
    return sum(valores) // len(valores)


def promedio_ponderado(valores: Sequence[float], pesos: Sequence[float]) -> float:
    if len(valores) != len(pesos):
        raise ValueError("valores y pesos deben tener la misma longitud")
    total_pesos = sum(pesos)
    if total_pesos == 0:
        raise ValueError("la suma de los pesos no puede ser cero")
    return sum(v * p for v, p in zip(valores, pesos)) / total_pesos


def mediana(valores: Iterable[float]) -> float:
    ordenados = sorted(valores)
    if not ordenados:
        raise ValueError("no se puede calcular la mediana de una secuencia vacía")
    medio = len(ordenados) // 2
    if len(ordenados) % 2:
        return float(ordenados[medio])
    return (ordenados[medio - 1] + ordenados[medio]) / 2


def moda(valores: Iterable[Any]) -> Any:
    """Valor más frecuente; en empate regresa el menor."""
    conteo = Counter(valores)
    if not conteo:
        raise ValueError("no se puede calcular la moda de una secuencia vacía")
    maximo = max(conteo.values())
    return min(v for v, c in conteo.items() if c == maximo)


def varianza(valores: Iterable[float], muestral: bool = True) -> float:
    valores = list(valores)
    n = len(valores)
    if n < 2:
        raise ValueError("se requieren al menos dos valores")
    media = promedio(valores)
    suma_cuadrados = sum((v - media) ** 2 for v in valores)
    return suma_cuadrados / (n - 1 if muestral else n)


def desviacion_estandar(valores: Iterable[float], muestral: bool = True) -> float:
    return math.sqrt(varianza(valores, muestral))


def percentil(valores: Iterable[float], p: float) -> float:
    """Percentil con interpolación lineal (mismo criterio que numpy por defecto)."""
    if not 0 <= p <= 100:
        raise ValueError("p debe estar entre 0 y 100")
    ordenados = sorted(valores)
    if not ordenados:
        raise ValueError("secuencia vacía")
    k = (len(ordenados) - 1) * p / 100
    piso, techo = math.floor(k), math.ceil(k)
    if piso == techo:
        return float(ordenados[int(k)])
    return ordenados[piso] + (ordenados[techo] - ordenados[piso]) * (k - piso)


def media_movil(valores: Sequence[float], ventana: int) -> List[float]:
    if ventana <= 0:
        raise ValueError("la ventana debe ser positiva")
    resultado = []
    suma = 0.0
    for i, valor in enumerate(valores):
        suma += valor
        if i >= ventana:
            suma -= valores[i - ventana]
        if i >= ventana - 1:
            resultado.append(round(suma / ventana, 6))
    return resultado


def normalizar_min_max(valores: Sequence[float]) -> List[float]:
    minimo, maximo = min(valores), max(valores)
    if minimo == maximo:
        return [0.0 for _ in valores]
    return [(v - minimo) / (maximo - minimo) for v in valores]


def puntaje_z(valores: Sequence[float]) -> List[float]:
    media = promedio(valores)
    desviacion = desviacion_estandar(valores)
    if desviacion == 0:
        return [0.0 for _ in valores]
    return [(v - media) / desviacion for v in valores]


def correlacion_pearson(x: Sequence[float], y: Sequence[float]) -> float:
    if len(x) != len(y) or len(x) < 2:
        raise ValueError("se requieren dos secuencias de igual longitud (n >= 2)")
    mx, my = promedio(x), promedio(y)
    cov = sum((a - mx) * (b - my) for a, b in zip(x, y))
    sx = math.sqrt(sum((a - mx) ** 2 for a in x))
    sy = math.sqrt(sum((b - my) ** 2 for b in y))
    if sx == 0 or sy == 0:
        raise ValueError("una de las secuencias es constante")
    return cov / (sx * sy)


def regresion_lineal_simple(x: Sequence[float], y: Sequence[float]) -> Tuple[float, float]:
    """Regresa (pendiente, intercepto) por mínimos cuadrados."""
    if len(x) != len(y) or len(x) < 2:
        raise ValueError("se requieren dos secuencias de igual longitud (n >= 2)")
    mx, my = promedio(x), promedio(y)
    sxx = sum((a - mx) ** 2 for a in x)
    if sxx == 0:
        raise ValueError("x es constante")
    sxy = sum((a - mx) * (b - my) for a, b in zip(x, y))
    pendiente = sxy / sxx
    return pendiente, my - pendiente * mx


# ==============================================================================
# SECCIÓN 7. MATEMÁTICAS FINANCIERAS
# ==============================================================================


def interes_compuesto(capital: float, tasa_anual: float, anios: float, capitalizaciones: int = 12) -> float:
    return capital * (1 + tasa_anual / capitalizaciones) ** (capitalizaciones * anios)


def valor_presente(monto_futuro: float, tasa_anual: float, anios: float, capitalizaciones: int = 12) -> float:
    return monto_futuro / (1 + tasa_anual / capitalizaciones) ** (capitalizaciones * anios)


def pago_mensual(principal: float, tasa_anual: float, meses: int) -> float:
    if meses <= 0:
        raise ValueError("el plazo debe ser positivo")
    if tasa_anual == 0:
        return principal / meses
    r = tasa_anual / 12
    return principal * r / (1 - (1 + r) ** -meses)


def tabla_amortizacion(principal: float, tasa_anual: float, meses: int) -> List[Dict[str, float]]:
    pago = pago_mensual(principal, tasa_anual, meses)
    r = tasa_anual / 12
    saldo = principal
    filas = []
    for periodo in range(1, meses + 1):
        interes = saldo * r
        abono = pago - interes
        saldo -= abono
        filas.append({
            "periodo": periodo,
            "pago": round(pago, 2),
            "interes": round(interes, 2),
            "abono_capital": round(abono, 2),
            "saldo": round(max(saldo, 0.0), 2),
        })
    return filas


def tasa_interna_retorno(flujos: Sequence[float], estimacion: float = 0.1, iteraciones: int = 200) -> float:
    """TIR por el método de Newton-Raphson."""
    tasa = estimacion
    for _ in range(iteraciones):
        vpn = sum(f / (1 + tasa) ** t for t, f in enumerate(flujos))
        derivada = sum(-t * f / (1 + tasa) ** (t + 1) for t, f in enumerate(flujos))
        if derivada == 0:
            break
        nueva = tasa - vpn / derivada
        if abs(nueva - tasa) < 1e-10:
            return nueva
        tasa = nueva
    return tasa


def valor_presente_neto(tasa: float, flujos: Sequence[float]) -> float:
    return sum(f / (1 + tasa) ** t for t, f in enumerate(flujos))


def depreciacion_linea_recta(costo: float, valor_residual: float, vida_util_anios: int) -> List[float]:
    if vida_util_anios <= 0:
        raise ValueError("la vida útil debe ser positiva")
    cuota = (costo - valor_residual) / vida_util_anios
    return [round(costo - cuota * anio, 2) for anio in range(1, vida_util_anios + 1)]


# ==============================================================================
# SECCIÓN 8. ESTRUCTURAS DE DATOS
# ==============================================================================

_SIN_VALOR = object()


class LRUCache:
    """Caché con política de reemplazo 'menos recientemente usado'."""

    def __init__(self, capacidad: int):
        if capacidad <= 0:
            raise ValueError("la capacidad debe ser positiva")
        self.capacidad = capacidad
        self._datos: "OrderedDict[Any, Any]" = OrderedDict()
        self.aciertos = 0
        self.fallos = 0

    def obtener(self, clave: Any, por_defecto: Any = None) -> Any:
        if clave not in self._datos:
            self.fallos += 1
            return por_defecto
        self.aciertos += 1
        return self._datos[clave]

    def guardar(self, clave: Any, valor: Any) -> None:
        if clave in self._datos:
            self._datos.move_to_end(clave)
        self._datos[clave] = valor
        if len(self._datos) > self.capacidad:
            self._datos.popitem(last=False)

    def eliminar(self, clave: Any) -> bool:
        if clave in self._datos:
            del self._datos[clave]
            return True
        return False

    def limpiar(self) -> None:
        self._datos.clear()
        self.aciertos = 0
        self.fallos = 0

    def claves(self) -> List[Any]:
        """Claves de la menos a la más recientemente usada."""
        return list(self._datos.keys())

    def tasa_aciertos(self) -> float:
        total = self.aciertos + self.fallos
        return self.aciertos / total if total else 0.0

    def __contains__(self, clave: Any) -> bool:
        return clave in self._datos

    def __len__(self) -> int:
        return len(self._datos)


def memoizar(capacidad: int = 128) -> Callable:
    """Decorador que memoiza una función de argumentos posicionales hashables."""

    def decorador(funcion: Callable) -> Callable:
        cache = LRUCache(capacidad)

        @functools.wraps(funcion)
        def envoltura(*args: Any) -> Any:
            valor = cache.obtener(args, _SIN_VALOR)
            if valor is _SIN_VALOR:
                valor = funcion(*args)
                cache.guardar(args, valor)
            return valor

        envoltura.cache = cache  # type: ignore[attr-defined]
        return envoltura

    return decorador


class Pila:
    def __init__(self, elementos: Iterable[Any] = ()):
        self._elementos = list(elementos)

    def apilar(self, elemento: Any) -> None:
        self._elementos.append(elemento)

    def desapilar(self) -> Any:
        if not self._elementos:
            raise IndexError("la pila está vacía")
        return self._elementos.pop()

    def cima(self) -> Any:
        if not self._elementos:
            raise IndexError("la pila está vacía")
        return self._elementos[-1]

    def esta_vacia(self) -> bool:
        return not self._elementos

    def __len__(self) -> int:
        return len(self._elementos)


class Cola:
    def __init__(self, elementos: Iterable[Any] = ()):
        self._elementos: deque = deque(elementos)

    def encolar(self, elemento: Any) -> None:
        self._elementos.append(elemento)

    def desencolar(self) -> Any:
        if not self._elementos:
            raise IndexError("la cola está vacía")
        return self._elementos.popleft()

    def frente(self) -> Any:
        if not self._elementos:
            raise IndexError("la cola está vacía")
        return self._elementos[0]

    def esta_vacia(self) -> bool:
        return not self._elementos

    def __len__(self) -> int:
        return len(self._elementos)


class ColaPrioridad:
    """Cola de prioridad mínima estable (a igual prioridad, sale primero el más antiguo)."""

    def __init__(self) -> None:
        self._monticulo: List[Tuple[Any, int, Any]] = []
        self._contador = itertools.count()

    def agregar(self, elemento: Any, prioridad: Any) -> None:
        heapq.heappush(self._monticulo, (prioridad, next(self._contador), elemento))

    def extraer(self) -> Any:
        if not self._monticulo:
            raise IndexError("la cola de prioridad está vacía")
        return heapq.heappop(self._monticulo)[2]

    def ver(self) -> Any:
        if not self._monticulo:
            raise IndexError("la cola de prioridad está vacía")
        return self._monticulo[0][2]

    def __len__(self) -> int:
        return len(self._monticulo)

    def __bool__(self) -> bool:
        return bool(self._monticulo)


_FIN_PALABRA = "\0"


class Trie:
    """Árbol de prefijos para autocompletar descripciones de productos."""

    def __init__(self, palabras: Iterable[str] = ()):
        self._raiz: Dict[str, Any] = {}
        self._tamano = 0
        for palabra in palabras:
            self.insertar(palabra)

    def insertar(self, palabra: str) -> None:
        nodo = self._raiz
        for caracter in palabra:
            nodo = nodo.setdefault(caracter, {})
        if _FIN_PALABRA not in nodo:
            nodo[_FIN_PALABRA] = True
            self._tamano += 1

    def _nodo(self, prefijo: str) -> Optional[Dict[str, Any]]:
        nodo = self._raiz
        for caracter in prefijo:
            if caracter not in nodo:
                return None
            nodo = nodo[caracter]
        return nodo

    def contiene(self, palabra: str) -> bool:
        nodo = self._nodo(palabra)
        return nodo is not None and _FIN_PALABRA in nodo

    def con_prefijo(self, prefijo: str, limite: Optional[int] = None) -> List[str]:
        nodo = self._nodo(prefijo)
        if nodo is None:
            return []
        resultados = []
        pendientes = [(nodo, prefijo)]
        while pendientes:
            actual, texto = pendientes.pop()
            if _FIN_PALABRA in actual:
                resultados.append(texto)
            for caracter, hijo in actual.items():
                if caracter != _FIN_PALABRA:
                    pendientes.append((hijo, texto + caracter))
        resultados.sort()
        return resultados[:limite] if limite else resultados

    def eliminar(self, palabra: str) -> bool:
        nodo = self._nodo(palabra)
        if nodo is None or _FIN_PALABRA not in nodo:
            return False
        del nodo[_FIN_PALABRA]
        self._tamano -= 1
        return True

    def __len__(self) -> int:
        return self._tamano


class UnionFind:
    """Conjuntos disjuntos con compresión de caminos y unión por rango."""

    def __init__(self, elementos: Iterable[Any] = ()):
        self._padre: Dict[Any, Any] = {}
        self._rango: Dict[Any, int] = {}
        self.componentes = 0
        for elemento in elementos:
            self.agregar(elemento)

    def agregar(self, elemento: Any) -> None:
        if elemento not in self._padre:
            self._padre[elemento] = elemento
            self._rango[elemento] = 0
            self.componentes += 1

    def encontrar(self, elemento: Any) -> Any:
        self.agregar(elemento)
        raiz = elemento
        while self._padre[raiz] != raiz:
            raiz = self._padre[raiz]
        while self._padre[elemento] != raiz:
            siguiente = self._padre[elemento]
            self._padre[elemento] = raiz
            elemento = siguiente
        return raiz

    def unir(self, a: Any, b: Any) -> bool:
        raiz_a, raiz_b = self.encontrar(a), self.encontrar(b)
        if raiz_a == raiz_b:
            return False
        if self._rango[raiz_a] < self._rango[raiz_b]:
            raiz_a, raiz_b = raiz_b, raiz_a
        self._padre[raiz_b] = raiz_a
        if self._rango[raiz_a] == self._rango[raiz_b]:
            self._rango[raiz_a] += 1
        self.componentes -= 1
        return True

    def conectados(self, a: Any, b: Any) -> bool:
        return self.encontrar(a) == self.encontrar(b)

    def grupos(self) -> List[List[Any]]:
        agrupados: Dict[Any, List[Any]] = defaultdict(list)
        for elemento in self._padre:
            agrupados[self.encontrar(elemento)].append(elemento)
        return sorted((sorted(g) for g in agrupados.values()), key=lambda g: (len(g), g))


class FiltroBloom:
    """Filtro de Bloom para verificar rápidamente si un folio ya fue procesado."""

    def __init__(self, tamano_bits: int = 2048, num_hashes: int = 3):
        if tamano_bits <= 0 or num_hashes <= 0:
            raise ValueError("parámetros inválidos")
        self.tamano_bits = tamano_bits
        self.num_hashes = num_hashes
        self._bits = bytearray((tamano_bits + 7) // 8)
        self.elementos = 0

    def _posiciones(self, valor: Any) -> Iterator[int]:
        datos = str(valor).encode("utf-8")
        for semilla in range(self.num_hashes):
            resumen = hashlib.sha256(bytes([semilla]) + datos).digest()
            yield int.from_bytes(resumen[:8], "big") % self.tamano_bits

    def agregar(self, valor: Any) -> None:
        for posicion in self._posiciones(valor):
            self._bits[posicion // 8] |= 1 << (posicion % 8)
        self.elementos += 1

    def posiblemente_contiene(self, valor: Any) -> bool:
        return all(self._bits[p // 8] & (1 << (p % 8)) for p in self._posiciones(valor))

    def tasa_falsos_positivos_estimada(self) -> float:
        k, m, n = self.num_hashes, self.tamano_bits, self.elementos
        return (1 - math.exp(-k * n / m)) ** k


# ==============================================================================
# SECCIÓN 9. BÚSQUEDA Y ORDENAMIENTO
# ==============================================================================


def busqueda_binaria(lista: Sequence[Any], objetivo: Any) -> int:
    """Índice de ``objetivo`` en ``lista`` (ordenada ascendentemente) o -1 si no está."""
    izquierda, derecha = 0, len(lista) - 1
    while izquierda < derecha:
        medio = (izquierda + derecha) // 2
        if lista[medio] == objetivo:
            return medio
        if lista[medio] < objetivo:
            izquierda = medio + 1
        else:
            derecha = medio - 1
    return -1


def insertar_ordenado(lista: List[Any], valor: Any) -> int:
    """Inserta manteniendo el orden; regresa la posición de inserción."""
    posicion = bisect.bisect_right(lista, valor)
    lista.insert(posicion, valor)
    return posicion


def merge_sort(elementos: Iterable[Any], clave: Optional[Callable[[Any], Any]] = None) -> List[Any]:
    """Ordenamiento por mezcla (estable)."""
    clave = clave or (lambda x: x)
    elementos = list(elementos)
    if len(elementos) <= 1:
        return elementos
    medio = len(elementos) // 2
    izquierda = merge_sort(elementos[:medio], clave)
    derecha = merge_sort(elementos[medio:], clave)
    resultado = []
    i = j = 0
    while i < len(izquierda) and j < len(derecha):
        if clave(derecha[j]) < clave(izquierda[i]):
            resultado.append(derecha[j])
            j += 1
        else:
            resultado.append(izquierda[i])
            i += 1
    resultado.extend(izquierda[i:])
    resultado.extend(derecha[j:])
    return resultado


def quick_sort(elementos: Iterable[Any]) -> List[Any]:
    """Quicksort de tres vías (maneja bien valores repetidos)."""
    elementos = list(elementos)
    if len(elementos) <= 1:
        return elementos
    pivote = elementos[len(elementos) // 2]
    menores = [x for x in elementos if x < pivote]
    iguales = [x for x in elementos if x == pivote]
    mayores = [x for x in elementos if x > pivote]
    return quick_sort(menores) + iguales + quick_sort(mayores)


def insertion_sort(elementos: Iterable[Any]) -> List[Any]:
    resultado = list(elementos)
    for i in range(1, len(resultado)):
        actual = resultado[i]
        j = i - 1
        while j >= 0 and resultado[j] > actual:
            resultado[j + 1] = resultado[j]
            j -= 1
        resultado[j + 1] = actual
    return resultado


def heap_sort(elementos: Iterable[Any]) -> List[Any]:
    monticulo = list(elementos)
    heapq.heapify(monticulo)
    return [heapq.heappop(monticulo) for _ in range(len(monticulo))]


def top_k(elementos: Iterable[Any], k: int, clave: Optional[Callable[[Any], Any]] = None) -> List[Any]:
    return heapq.nlargest(k, elementos, key=clave)


# ==============================================================================
# SECCIÓN 10. UTILERÍAS DE COLECCIONES
# ==============================================================================


def paginar(elementos: Sequence[Any], pagina: int, tamano: int) -> Dict[str, Any]:
    if pagina < 1 or tamano < 1:
        raise ValueError("página y tamaño deben ser positivos")
    total = len(elementos)
    total_paginas = max(1, math.ceil(total / tamano))
    inicio = (pagina - 1) * tamano
    return {
        "pagina": pagina,
        "tamano": tamano,
        "total": total,
        "total_paginas": total_paginas,
        "elementos": list(elementos[inicio:inicio + tamano]),
        "tiene_siguiente": pagina < total_paginas,
        "tiene_anterior": pagina > 1,
    }


def agrupar_por(elementos: Iterable[Any], clave: Callable[[Any], Any]) -> Dict[Any, List[Any]]:
    grupos: Dict[Any, List[Any]] = defaultdict(list)
    for elemento in elementos:
        grupos[clave(elemento)].append(elemento)
    return dict(grupos)


def contar_por(elementos: Iterable[Any], clave: Callable[[Any], Any]) -> Dict[Any, int]:
    return dict(Counter(clave(e) for e in elementos))


def indexar_por(elementos: Iterable[Any], clave: Callable[[Any], Any]) -> Dict[Any, Any]:
    indice: Dict[Any, Any] = {}
    for elemento in elementos:
        k = clave(elemento)
        if k in indice:
            raise ValueError(f"clave duplicada al indexar: {k!r}")
        indice[k] = elemento
    return indice


def aplanar(anidada: Iterable[Any]) -> List[Any]:
    resultado: List[Any] = []
    for elemento in anidada:
        if isinstance(elemento, (list, tuple)):
            resultado.extend(aplanar(elemento))
        else:
            resultado.append(elemento)
    return resultado


def dividir_en_bloques(elementos: Sequence[Any], tamano: int) -> List[List[Any]]:
    if tamano <= 0:
        raise ValueError("el tamaño de bloque debe ser positivo")
    return [list(elementos[i:i + tamano]) for i in range(0, len(elementos), tamano)]


def unicos_preservando_orden(elementos: Iterable[Any]) -> List[Any]:
    vistos = set()
    resultado = []
    for elemento in elementos:
        if elemento not in vistos:
            vistos.add(elemento)
            resultado.append(elemento)
    return resultado


def ventana_deslizante(elementos: Iterable[Any], tamano: int) -> Iterator[Tuple[Any, ...]]:
    ventana: deque = deque(maxlen=tamano)
    for elemento in elementos:
        ventana.append(elemento)
        if len(ventana) == tamano:
            yield tuple(ventana)


# ==============================================================================
# SECCIÓN 11. REPORTES EN TEXTO PLANO
# ==============================================================================

_PATRON_NUMERICO = re.compile(r"^-?\$?[\d,]+(\.\d+)?%?$")


def _celda_a_texto(valor: Any) -> str:
    if valor is None:
        return ""
    if isinstance(valor, bool):
        return "Sí" if valor else "No"
    if isinstance(valor, float):
        return f"{valor:,.2f}"
    return str(valor)


def tabla_texto(encabezados: Sequence[str], filas: Sequence[Sequence[Any]], separador: str = " | ") -> str:
    """Tabla alineada; las columnas numéricas se justifican a la derecha."""
    celdas = [[_celda_a_texto(c) for c in fila] for fila in filas]
    anchos = [len(str(h)) for h in encabezados]
    for fila in celdas:
        if len(fila) != len(encabezados):
            raise ValueError("todas las filas deben tener tantas columnas como encabezados")
        for i, celda in enumerate(fila):
            anchos[i] = max(anchos[i], len(celda))
    numericas = [bool(celdas) and all(_PATRON_NUMERICO.match(f[i]) for f in celdas) for i in range(len(encabezados))]

    def formatear(fila: Sequence[str]) -> str:
        partes = [c.rjust(anchos[i]) if numericas[i] else c.ljust(anchos[i]) for i, c in enumerate(fila)]
        return separador.join(partes).rstrip()

    lineas = [formatear([str(h) for h in encabezados]), "-+-".join("-" * a for a in anchos)]
    lineas.extend(formatear(f) for f in celdas)
    return "\n".join(lineas)


def histograma_texto(conteos: Dict[Any, float], ancho: int = 40, caracter: str = "#") -> str:
    if not conteos:
        return "(sin datos)"
    maximo = max(conteos.values())
    ancho_etiqueta = max(len(str(k)) for k in conteos)
    lineas = []
    for clave, valor in conteos.items():
        barra = caracter * (int(round(valor / maximo * ancho)) if maximo else 0)
        lineas.append(f"{str(clave).ljust(ancho_etiqueta)} | {barra} {valor}")
    return "\n".join(lineas)


def _serializador_json(objeto: Any) -> Any:
    if isinstance(objeto, (date, datetime)):
        return objeto.isoformat()
    if hasattr(objeto, "__dataclass_fields__"):
        return asdict(objeto)
    if isinstance(objeto, set):
        return sorted(objeto)
    if isinstance(objeto, Decimal):
        return float(objeto)
    raise TypeError(f"no serializable: {type(objeto).__name__}")


def a_json(objeto: Any, indent: Optional[int] = 2) -> str:
    return json.dumps(objeto, default=_serializador_json, ensure_ascii=False, indent=indent)


def encabezado_reporte(titulo: str, ancho: int = 78) -> str:
    return "\n".join(["=" * ancho, titulo.center(ancho), f"{NOMBRE_EMPRESA} - v{VERSION}".center(ancho), "=" * ancho])


# ==============================================================================
# SECCIÓN 12. REPOSITORIO GENÉRICO EN MEMORIA
# ==============================================================================


class RepositorioMemoria:
    """Repositorio genérico para entidades tipo dataclass con campo entero ``id``."""

    entidad: Any = None
    nombre: str = "registros"

    def __init__(self, validar_al_guardar: bool = True):
        self._items: Dict[int, Any] = {}
        self.validar_al_guardar = validar_al_guardar
        self._observadores: List[Callable[[str, Any], None]] = []

    # --- eventos ----------------------------------------------------------
    def suscribir(self, observador: Callable[[str, Any], None]) -> None:
        self._observadores.append(observador)

    def _notificar(self, evento: str, registro: Any) -> None:
        for observador in list(self._observadores):
            observador(evento, registro)

    # --- validación -------------------------------------------------------
    def _validar(self, registro: Any) -> None:
        if self.entidad is not None and not isinstance(registro, self.entidad):
            raise TypeError(
                f"{self.nombre}: se esperaba {self.entidad.__name__}, se recibió {type(registro).__name__}"
            )
        if self.validar_al_guardar:
            errores = registro.validar()
            if errores:
                raise ErrorValidacion(type(registro).__name__, errores)

    # --- CRUD -------------------------------------------------------------
    def agregar(self, registro: Any) -> Any:
        self._validar(registro)
        if registro.id in self._items:
            raise ErrorSistema(f"{self.nombre}: ya existe un registro con id={registro.id}")
        self._items[registro.id] = registro
        self._notificar("alta", registro)
        return registro

    def agregar_varios(self, registros: Iterable[Any]) -> int:
        cuenta = 0
        for registro in registros:
            self.agregar(registro)
            cuenta += 1
        return cuenta

    def siguiente_id(self) -> int:
        return max(self._items, default=0) + 1

    def obtener(self, id_: int) -> Any:
        try:
            return self._items[id_]
        except KeyError:
            raise EntidadNoEncontrada(f"{self.nombre}: no existe el id {id_}") from None

    def existe(self, id_: int) -> bool:
        return id_ in self._items

    def actualizar(self, id_: int, **cambios: Any) -> Any:
        if "id" in cambios and cambios["id"] != id_:
            raise ErrorSistema("no se permite cambiar el id de un registro")
        actual = self.obtener(id_)
        nuevo = replace(actual, **cambios)
        self._validar(nuevo)
        self._items[id_] = nuevo
        self._notificar("cambio", nuevo)
        return nuevo

    def eliminar(self, id_: int) -> Any:
        registro = self.obtener(id_)
        del self._items[id_]
        self._notificar("baja", registro)
        return registro

    def limpiar(self) -> None:
        self._items.clear()

    # --- consultas --------------------------------------------------------
    def listar(self) -> List[Any]:
        return [self._items[k] for k in sorted(self._items)]

    def contar(self, predicado: Optional[Callable[[Any], bool]] = None) -> int:
        if predicado is None:
            return len(self._items)
        return sum(1 for r in self._items.values() if predicado(r))

    def filtrar(self, predicado: Callable[[Any], bool]) -> List[Any]:
        return [r for r in self.listar() if predicado(r)]

    def buscar(self, **criterios: Any) -> List[Any]:
        if self.entidad is not None:
            validos = {f.name for f in fields(self.entidad)}
            for campo in criterios:
                if campo not in validos:
                    raise AttributeError(f"{self.entidad.__name__} no tiene el campo '{campo}'")
        return [r for r in self.listar() if all(getattr(r, c) == v for c, v in criterios.items())]

    def primero(self, predicado: Optional[Callable[[Any], bool]] = None) -> Optional[Any]:
        for registro in self.listar():
            if predicado is None or predicado(registro):
                return registro
        return None

    def ordenar_por(self, campo: str, descendente: bool = False) -> List[Any]:
        return sorted(self.listar(), key=lambda r: (getattr(r, campo), r.id), reverse=descendente)

    def paginar(self, pagina: int = 1, tamano: int = 10) -> Dict[str, Any]:
        return paginar(self.listar(), pagina, tamano)

    def valores(self, campo: str) -> List[Any]:
        return [getattr(r, campo) for r in self.listar()]

    def agrupar(self, campo: str) -> Dict[Any, List[Any]]:
        return agrupar_por(self.listar(), lambda r: getattr(r, campo))

    def conteo_por(self, campo: str) -> Dict[Any, int]:
        return dict(Counter(getattr(r, campo) for r in self._items.values()))

    def __len__(self) -> int:
        return len(self._items)

    def __iter__(self) -> Iterator[Any]:
        return iter(self.listar())

    def __contains__(self, id_: int) -> bool:
        return id_ in self._items

    # --- importación / exportación ---------------------------------------
    def _nombres_campos(self) -> List[str]:
        if self.entidad is None:
            raise ErrorSistema(f"{self.nombre}: el repositorio no tiene entidad asociada")
        return [f.name for f in fields(self.entidad)]

    def a_dicts(self) -> List[Dict[str, Any]]:
        return [r.a_dict() for r in self.listar()]

    def exportar_csv(self) -> str:
        salida = io.StringIO()
        escritor = csv.DictWriter(salida, fieldnames=self._nombres_campos(), lineterminator="\n")
        escritor.writeheader()
        for registro in self.listar():
            escritor.writerow(registro.a_dict())
        return salida.getvalue()

    def importar_csv(self, texto: str) -> int:
        lector = csv.DictReader(io.StringIO(texto))
        return self.agregar_varios(self.entidad.desde_dict(fila) for fila in lector)

    def exportar_json(self, indent: Optional[int] = None) -> str:
        return json.dumps(self.a_dicts(), ensure_ascii=False, indent=indent)

    def importar_json(self, texto: str) -> int:
        return self.agregar_varios(self.entidad.desde_dict(d) for d in json.loads(texto))


# ==============================================================================
# SECCIÓN 13. DATOS DE DEMOSTRACIÓN
# ==============================================================================

NOMBRES_DEMO = (
    "María", "José", "Juan", "Guadalupe", "Luis", "Ana", "Carlos", "Fernanda", "Jorge", "Sofía",
    "Miguel", "Valeria", "Ricardo", "Daniela", "Alejandro", "Paola", "Roberto", "Lucía", "Héctor", "Ximena",
)
APELLIDOS_DEMO = (
    "Hernández", "García", "Martínez", "López", "González", "Pérez", "Rodríguez", "Sánchez", "Ramírez", "Cruz",
    "Flores", "Gómez", "Morales", "Vázquez", "Jiménez", "Reyes", "Díaz", "Torres", "Gutiérrez", "Ruiz",
)
EMPRESAS_DEMO = (
    "Distribuidora", "Comercializadora", "Abastecedora", "Grupo", "Productos",
    "Lácteos", "Granos", "Bebidas", "Empacadora", "Industrias",
)
GIROS_DEMO = (
    "del Bajío", "de Occidente", "Tapatía", "del Centro", "La Perla",
    "Los Altos", "Santa Fe", "El Sol", "Real", "Continental",
)
SUFIJOS_EMPRESA = ("S.A. de C.V.", "S. de R.L. de C.V.", "S.A.P.I. de C.V.", "S.C.")
CIUDADES_DEMO = (
    "Guadalajara", "Zapopan", "Tlaquepaque", "Tonalá", "Tlajomulco", "León", "Irapuato",
    "Celaya", "Morelia", "Aguascalientes", "Querétaro", "Zacatecas", "Lagos de Moreno", "Tepatitlán",
)
MARCAS_DEMO = (
    "La Huerta Fina", "Don Chema", "Sabor Real", "El Granero", "Campo Dorado", "Lácteos San Isidro",
    "Doña Lupe", "Rancho Viejo", "Maizal", "Puro Norte", "Delicias del Valle", "Marca Propia",
)
PRODUCTOS_DEMO = (
    "Frijol bayo", "Arroz súper extra", "Aceite vegetal", "Azúcar estándar", "Harina de maíz",
    "Leche entera", "Atún en agua", "Galletas marías", "Café soluble", "Refresco de cola",
    "Agua purificada", "Jabón de lavandería", "Papel higiénico", "Detergente en polvo",
    "Chiles en vinagre", "Sopa de pasta", "Mayonesa", "Cereal de maíz", "Huevo blanco",
    "Tortillas de harina",
)
PRESENTACIONES_DEMO = ("500 g", "1 kg", "900 ml", "1 L", "2 L", "4 rollos", "12 pzas", "250 g", "355 ml", "5 kg")
NOMBRES_CATEGORIA_DEMO = (
    "Abarrotes", "Lácteos", "Bebidas", "Limpieza", "Higiene personal", "Botanas",
    "Panadería", "Enlatados", "Granos y semillas", "Mascotas", "Desechables", "Dulcería",
)
DOMINIOS_DEMO = ("correo.mx", "ejemplo.com", "abarrotesbajio.mx", "proveedores.com.mx", "mail.com")
PALABRAS_DEMO = (
    "revisión", "entrega", "urgente", "pendiente", "cliente", "sucursal", "mercancía", "factura",
    "seguimiento", "autorizado", "lote", "temporada", "inventario", "faltante", "sobrante", "calidad",
)
TALLERES_DEMO = (
    "Taller Mecánico Hermanos Ruiz", "Servicio Automotriz del Bajío", "Llantera La Rueda",
    "Diesel Center GDL", "Autoservicio Express",
)
CONCEPTOS_GASTO_DEMO = (
    "Renta de local", "Recibo de energía eléctrica", "Recibo de agua", "Publicidad en radio",
    "Compra de papelería", "Mantenimiento de refrigeradores", "Servicio de limpieza",
    "Vigilancia", "Fumigación", "Internet y telefonía",
)


def nombre_persona_demo(rng: random.Random) -> str:
    return f"{rng.choice(NOMBRES_DEMO)} {rng.choice(APELLIDOS_DEMO)} {rng.choice(APELLIDOS_DEMO)}"


def razon_social_demo(rng: random.Random) -> str:
    return f"{rng.choice(EMPRESAS_DEMO)} {rng.choice(GIROS_DEMO)} {rng.choice(SUFIJOS_EMPRESA)}"


def frase_demo(rng: random.Random, palabras: int = 4) -> str:
    return " ".join(rng.choice(PALABRAS_DEMO) for _ in range(palabras)).capitalize()


def codigo_aleatorio(rng: random.Random, longitud: int, alfabeto: str = LETRAS + DIGITOS) -> str:
    return "".join(rng.choice(alfabeto) for _ in range(longitud))


def fecha_aleatoria_demo(rng: random.Random, inicio: date = date(2024, 1, 1), fin: date = date(2026, 12, 31)) -> str:
    return (inicio + timedelta(days=rng.randint(0, (fin - inicio).days))).isoformat()


def generar_rfc_demo(rng: random.Random, moral: bool = False) -> str:
    prefijo = codigo_aleatorio(rng, 3 if moral else 4, LETRAS)
    nacimiento = date(1950, 1, 1) + timedelta(days=rng.randint(0, 25000))
    return f"{prefijo}{nacimiento:%y%m%d}{codigo_aleatorio(rng, 3)}"


def generar_ean13_demo(rng: random.Random, prefijo: str = "750") -> str:
    cuerpo = prefijo + "".join(rng.choice(DIGITOS) for _ in range(12 - len(prefijo)))
    return cuerpo + str(digito_verificador_ean13(cuerpo))


def telefono_demo(rng: random.Random, lada: str = "33") -> str:
    return lada + "".join(rng.choice(DIGITOS) for _ in range(10 - len(lada)))


def placas_demo(rng: random.Random) -> str:
    return f"{codigo_aleatorio(rng, 3, LETRAS)}-{rng.randint(0, 999):03d}-{rng.choice(LETRAS)}"


def ip_demo(rng: random.Random) -> str:
    return ".".join(str(rng.randint(1, 254)) for _ in range(4))


def sku_demo(rng: random.Random) -> str:
    return f"{codigo_aleatorio(rng, 3, LETRAS)}-{rng.randint(0, 99999):05d}"


def email_demo(rng: random.Random, base: Optional[str] = None) -> str:
    base = base or rng.choice(NOMBRES_DEMO)
    return f"{slugify(base).replace('-', '.')}{rng.randint(1, 999)}@{rng.choice(DOMINIOS_DEMO)}"


def hora_entrada_demo(rng: random.Random, tipo: str) -> str:
    if tipo == "nocturno":
        return "22:00"
    if tipo == "vespertino":
        return f"{rng.randint(13, 15):02d}:{rng.choice((0, 30)):02d}"
    return f"{rng.randint(6, 9):02d}:{rng.choice((0, 30)):02d}"


def hora_salida_demo(entrada: str, tipo: str, horas: int = 8) -> str:
    h, m = map(int, entrada.split(":"))
    total = (h * 60 + m + horas * 60) % (24 * 60)
    return f"{total // 60:02d}:{total % 60:02d}"


# ==============================================================================
# SECCIÓN 14. CATÁLOGO DE ENTIDADES DEL NEGOCIO
# ==============================================================================
#
# Cada entidad define: dataclass con validación, repositorio especializado,
# reporte en texto y generador de datos de demostración.


# ----------------------------------------------------------------------------
# Entidad: Proveedor  (Proveedores)
# ----------------------------------------------------------------------------

OPCIONES_PROVEEDOR_ESTATUS = ('activo', 'suspendido', 'baja')


@dataclass
class Proveedor:
    """Proveedor registrado en el catálogo maestro de compras."""

    id: int
    razon_social: str
    rfc: str
    estatus: str
    limite_credito: float
    fecha_alta: str
    contacto: str = ''
    email: str = ''
    telefono: str = ''
    dias_credito: int = 30

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.razon_social, str) or not self.razon_social.strip():
            errores.append("razon_social es obligatorio")
        elif len(self.razon_social) > 120:
            errores.append("razon_social excede 120 caracteres")
        if not es_rfc_valido(self.rfc):
            errores.append("rfc no es un RFC válido")
        if self.estatus not in OPCIONES_PROVEEDOR_ESTATUS:
            errores.append(f"estatus debe ser uno de: {', '.join(OPCIONES_PROVEEDOR_ESTATUS)}")
        if not isinstance(self.limite_credito, (int, float)) or isinstance(self.limite_credito, bool) or not 0 <= self.limite_credito <= 5_000_000:
            errores.append("limite_credito debe estar entre 0 y 5_000_000")
        if not es_fecha_iso(self.fecha_alta):
            errores.append("fecha_alta debe tener formato AAAA-MM-DD")
        if not isinstance(self.contacto, str):
            errores.append("contacto debe ser texto")
        elif len(self.contacto) > 80:
            errores.append("contacto excede 80 caracteres")
        if self.email and not es_email_valido(self.email):
            errores.append("email no es un correo válido")
        if self.telefono and not es_telefono_valido(self.telefono):
            errores.append("telefono debe tener 10 dígitos")
        if not isinstance(self.dias_credito, int) or isinstance(self.dias_credito, bool) or not 0 <= self.dias_credito <= 120:
            errores.append("dias_credito debe ser un entero entre 0 y 120")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Proveedor":
        return cls(
            id=int(datos["id"]),
            razon_social=str(datos["razon_social"]),
            rfc=str(datos["rfc"]),
            estatus=str(datos["estatus"]),
            limite_credito=float(datos["limite_credito"]),
            fecha_alta=str(datos["fecha_alta"]),
            contacto=str(datos.get("contacto", '')),
            email=str(datos.get("email", '')),
            telefono=str(datos.get("telefono", '')),
            dias_credito=int(datos.get("dias_credito", 30)),
        )


class RepositorioProveedores(RepositorioMemoria):
    """Repositorio en memoria de proveedores."""

    entidad = Proveedor
    nombre = "proveedores"
    CAMPOS_TEXTO = ('razon_social', 'contacto')

    def por_estatus(self, valor: str) -> List[Proveedor]:
        """Registros cuyo campo estatus es ``valor``."""
        if valor not in OPCIONES_PROVEEDOR_ESTATUS:
            raise ValueError(f"estatus inválido: {valor!r}")
        return [r for r in self.listar() if r.estatus == valor]

    def conteo_por_estatus(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_PROVEEDOR_ESTATUS}
        for registro in self._items.values():
            conteo[registro.estatus] += 1
        return conteo

    def total_limite_credito(self) -> float:
        return round(sum(r.limite_credito for r in self._items.values()), 2)

    def promedio_limite_credito(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.limite_credito for r in self._items.values()), 2)

    def con_limite_credito_entre(self, minimo: float, maximo: float) -> List[Proveedor]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.limite_credito <= maximo]

    def mayores_por_limite_credito(self, n: int = 5) -> List[Proveedor]:
        return sorted(self._items.values(), key=lambda r: (-r.limite_credito, r.id))[:n]

    def por_fecha_alta_entre(self, inicio: str, fin: str) -> List[Proveedor]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_alta and inicio <= r.fecha_alta <= fin]

    def conteo_mensual_fecha_alta(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_alta:
                conteo[registro.fecha_alta[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_dias_credito_entre(self, minimo: int, maximo: int) -> List[Proveedor]:
        return [r for r in self.listar() if minimo <= r.dias_credito <= maximo]

    def maximo_dias_credito(self) -> Optional[int]:
        valores = [r.dias_credito for r in self._items.values()]
        return max(valores) if valores else None

    def buscar_texto(self, termino: str) -> List[Proveedor]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_estatus": self.conteo_por_estatus(),
            "total_limite_credito": self.total_limite_credito(),
        }

    def con_credito(self) -> List[Proveedor]:
        """Proveedores activos que otorgan días de crédito."""
        return [p for p in self.listar() if p.estatus == "activo" and p.dias_credito > 0]


def reporte_proveedores(repo: RepositorioProveedores, limite: int = 25) -> str:
    """Listado en texto plano de proveedores."""
    encabezados = ['ID', 'Razón social', 'RFC', 'Estatus', 'Límite de crédito', 'Días crédito']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            truncar(r.razon_social, 28),
            r.rfc,
            r.estatus,
            formatear_moneda(r.limite_credito),
            r.dias_credito,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Proveedores ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_proveedores_demo(n: int = 10, semilla: int = 11) -> List[Proveedor]:
    """Genera ``n`` registros de proveedores reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Proveedor] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["razon_social"] = razon_social_demo(rng)
        v["rfc"] = generar_rfc_demo(rng, moral=True)
        v["estatus"] = rng.choice(("activo", "activo", "activo", "suspendido", "baja"))
        v["limite_credito"] = round(rng.uniform(10_000, 750_000), 2)
        v["fecha_alta"] = fecha_aleatoria_demo(rng)
        v["contacto"] = nombre_persona_demo(rng)
        v["email"] = email_demo(rng)
        v["telefono"] = telefono_demo(rng)
        v["dias_credito"] = rng.choice((0, 15, 30, 45, 60, 90))
        registros.append(Proveedor(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Categoria  (Categorías)
# ----------------------------------------------------------------------------

_PATRON_CATEGORIA_CLAVE = re.compile(r"^[A-Z]{3}$")


@dataclass
class Categoria:
    """Categoría de productos con su margen objetivo."""

    id: int
    nombre: str
    clave: str
    margen_objetivo: float
    descripcion: str = ''
    nivel: int = 1
    activa: bool = True

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 60:
            errores.append("nombre excede 60 caracteres")
        if not isinstance(self.clave, str) or not _PATRON_CATEGORIA_CLAVE.match(self.clave):
            errores.append("clave tiene un formato inválido")
        if not isinstance(self.margen_objetivo, (int, float)) or isinstance(self.margen_objetivo, bool) or not 0 <= self.margen_objetivo <= 90:
            errores.append("margen_objetivo debe estar entre 0 y 90")
        if not isinstance(self.descripcion, str):
            errores.append("descripcion debe ser texto")
        elif len(self.descripcion) > 200:
            errores.append("descripcion excede 200 caracteres")
        if not isinstance(self.nivel, int) or isinstance(self.nivel, bool) or not 1 <= self.nivel <= 4:
            errores.append("nivel debe ser un entero entre 1 y 4")
        if not isinstance(self.activa, bool):
            errores.append("activa debe ser booleano")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Categoria":
        return cls(
            id=int(datos["id"]),
            nombre=str(datos["nombre"]),
            clave=str(datos["clave"]),
            margen_objetivo=float(datos["margen_objetivo"]),
            descripcion=str(datos.get("descripcion", '')),
            nivel=int(datos.get("nivel", 1)),
            activa=a_booleano(datos.get("activa", True)),
        )

    def precio_sugerido(self, costo: float) -> float:
        """Precio sugerido para alcanzar el margen objetivo de la categoría."""
        if self.margen_objetivo >= 100:
            raise ValueError("el margen objetivo debe ser menor a 100%")
        return round(costo / (1 - self.margen_objetivo / 100), 2)


class RepositorioCategorias(RepositorioMemoria):
    """Repositorio en memoria de categorías."""

    entidad = Categoria
    nombre = "categorias"
    CAMPOS_TEXTO = ('nombre', 'descripcion')

    def con_clave(self, valor: str) -> List[Categoria]:
        return [r for r in self.listar() if r.clave == valor]

    def total_margen_objetivo(self) -> float:
        return round(sum(r.margen_objetivo for r in self._items.values()), 2)

    def promedio_margen_objetivo(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.margen_objetivo for r in self._items.values()), 2)

    def con_margen_objetivo_entre(self, minimo: float, maximo: float) -> List[Categoria]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.margen_objetivo <= maximo]

    def mayores_por_margen_objetivo(self, n: int = 5) -> List[Categoria]:
        return sorted(self._items.values(), key=lambda r: (-r.margen_objetivo, r.id))[:n]

    def con_nivel_entre(self, minimo: int, maximo: int) -> List[Categoria]:
        return [r for r in self.listar() if minimo <= r.nivel <= maximo]

    def maximo_nivel(self) -> Optional[int]:
        valores = [r.nivel for r in self._items.values()]
        return max(valores) if valores else None

    def donde_activa(self, valor: bool = True) -> List[Categoria]:
        return [r for r in self.listar() if r.activa is valor]

    def buscar_texto(self, termino: str) -> List[Categoria]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
        }


def reporte_categorias(repo: RepositorioCategorias, limite: int = 25) -> str:
    """Listado en texto plano de categorías."""
    encabezados = ['ID', 'Nombre', 'Clave', 'Margen objetivo', 'Descripcion', 'Nivel']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            truncar(r.nombre, 28),
            r.clave,
            f"{r.margen_objetivo:.2f}",
            truncar(r.descripcion, 28),
            r.nivel,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Categorías ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_categorias_demo(n: int = 10, semilla: int = 12) -> List[Categoria]:
    """Genera ``n`` registros de categorías reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Categoria] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["nombre"] = f"{rng.choice(NOMBRES_CATEGORIA_DEMO)} {i}"
        v["clave"] = codigo_aleatorio(rng, 3, LETRAS)
        v["margen_objetivo"] = round(rng.uniform(12, 45), 2)
        v["descripcion"] = frase_demo(rng, 6)
        v["nivel"] = rng.randint(1, 4)
        v["activa"] = rng.random() < 0.9
        registros.append(Categoria(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Producto  (Productos)
# ----------------------------------------------------------------------------

_PATRON_PRODUCTO_SKU = re.compile(r"^[A-Z]{3}-\d{5}$")
_PATRON_PRODUCTO_CATEGORIA_CLAVE = re.compile(r"^[A-Z]{3}$")
OPCIONES_PRODUCTO_UNIDAD = ('pieza', 'kg', 'litro', 'caja', 'paquete')
_PATRON_PRODUCTO_CODIGO_BARRAS = re.compile(r"^\d{13}$")


@dataclass
class Producto:
    """Producto del catálogo maestro (ficha comercial)."""

    id: int
    sku: str
    descripcion: str
    marca: str
    categoria_clave: str
    unidad: str
    precio_lista: float
    costo: float
    codigo_barras: str
    perecedero: bool = False
    existencia_minima: int = 5

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.sku, str) or not _PATRON_PRODUCTO_SKU.match(self.sku):
            errores.append("sku tiene un formato inválido")
        if not isinstance(self.descripcion, str) or not self.descripcion.strip():
            errores.append("descripcion es obligatorio")
        elif len(self.descripcion) > 120:
            errores.append("descripcion excede 120 caracteres")
        if not isinstance(self.marca, str) or not self.marca.strip():
            errores.append("marca es obligatorio")
        elif len(self.marca) > 60:
            errores.append("marca excede 60 caracteres")
        if not isinstance(self.categoria_clave, str) or not _PATRON_PRODUCTO_CATEGORIA_CLAVE.match(self.categoria_clave):
            errores.append("categoria_clave tiene un formato inválido")
        if self.unidad not in OPCIONES_PRODUCTO_UNIDAD:
            errores.append(f"unidad debe ser uno de: {', '.join(OPCIONES_PRODUCTO_UNIDAD)}")
        if not isinstance(self.precio_lista, (int, float)) or isinstance(self.precio_lista, bool) or not 0.5 <= self.precio_lista <= 20_000:
            errores.append("precio_lista debe estar entre 0.5 y 20_000")
        if not isinstance(self.costo, (int, float)) or isinstance(self.costo, bool) or not 0.1 <= self.costo <= 15_000:
            errores.append("costo debe estar entre 0.1 y 15_000")
        if not isinstance(self.codigo_barras, str) or not _PATRON_PRODUCTO_CODIGO_BARRAS.match(self.codigo_barras):
            errores.append("codigo_barras tiene un formato inválido")
        if not isinstance(self.perecedero, bool):
            errores.append("perecedero debe ser booleano")
        if not isinstance(self.existencia_minima, int) or isinstance(self.existencia_minima, bool) or not 0 <= self.existencia_minima <= 1000:
            errores.append("existencia_minima debe ser un entero entre 0 y 1000")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.costo > self.precio_lista:
                errores.append("el costo no puede ser mayor al precio de lista")
            if not validar_ean13(self.codigo_barras):
                errores.append("el código de barras tiene un dígito verificador inválido")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Producto":
        return cls(
            id=int(datos["id"]),
            sku=str(datos["sku"]),
            descripcion=str(datos["descripcion"]),
            marca=str(datos["marca"]),
            categoria_clave=str(datos["categoria_clave"]),
            unidad=str(datos["unidad"]),
            precio_lista=float(datos["precio_lista"]),
            costo=float(datos["costo"]),
            codigo_barras=str(datos["codigo_barras"]),
            perecedero=a_booleano(datos.get("perecedero", False)),
            existencia_minima=int(datos.get("existencia_minima", 5)),
        )

    @property
    def margen_pct(self) -> float:
        return margen_bruto(self.precio_lista, self.costo)


class RepositorioProductos(RepositorioMemoria):
    """Repositorio en memoria de productos."""

    entidad = Producto
    nombre = "productos"
    CAMPOS_TEXTO = ('descripcion', 'marca')

    def con_sku(self, valor: str) -> List[Producto]:
        return [r for r in self.listar() if r.sku == valor]

    def con_categoria_clave(self, valor: str) -> List[Producto]:
        return [r for r in self.listar() if r.categoria_clave == valor]

    def por_unidad(self, valor: str) -> List[Producto]:
        """Registros cuyo campo unidad es ``valor``."""
        if valor not in OPCIONES_PRODUCTO_UNIDAD:
            raise ValueError(f"unidad inválido: {valor!r}")
        return [r for r in self.listar() if r.unidad == valor]

    def conteo_por_unidad(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_PRODUCTO_UNIDAD}
        for registro in self._items.values():
            conteo[registro.unidad] += 1
        return conteo

    def total_precio_lista(self) -> float:
        return round(sum(r.precio_lista for r in self._items.values()), 2)

    def promedio_precio_lista(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.precio_lista for r in self._items.values()), 2)

    def con_precio_lista_entre(self, minimo: float, maximo: float) -> List[Producto]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.precio_lista <= maximo]

    def mayores_por_precio_lista(self, n: int = 5) -> List[Producto]:
        return sorted(self._items.values(), key=lambda r: (-r.precio_lista, r.id))[:n]

    def total_costo(self) -> float:
        return round(sum(r.costo for r in self._items.values()), 2)

    def promedio_costo(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.costo for r in self._items.values()), 2)

    def con_costo_entre(self, minimo: float, maximo: float) -> List[Producto]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.costo <= maximo]

    def mayores_por_costo(self, n: int = 5) -> List[Producto]:
        return sorted(self._items.values(), key=lambda r: (-r.costo, r.id))[:n]

    def con_codigo_barras(self, valor: str) -> List[Producto]:
        return [r for r in self.listar() if r.codigo_barras == valor]

    def donde_perecedero(self, valor: bool = True) -> List[Producto]:
        return [r for r in self.listar() if r.perecedero is valor]

    def con_existencia_minima_entre(self, minimo: int, maximo: int) -> List[Producto]:
        return [r for r in self.listar() if minimo <= r.existencia_minima <= maximo]

    def maximo_existencia_minima(self) -> Optional[int]:
        valores = [r.existencia_minima for r in self._items.values()]
        return max(valores) if valores else None

    def buscar_texto(self, termino: str) -> List[Producto]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_unidad": self.conteo_por_unidad(),
            "total_precio_lista": self.total_precio_lista(),
            "total_costo": self.total_costo(),
        }

    def por_sku(self, sku: str) -> Optional[Producto]:
        for producto in self._items.values():
            if producto.sku == sku:
                return producto
        return None

    def con_margen_menor_a(self, porcentaje: float) -> List[Producto]:
        return [p for p in self.listar() if p.margen_pct < porcentaje]


def reporte_productos(repo: RepositorioProductos, limite: int = 25) -> str:
    """Listado en texto plano de productos."""
    encabezados = ['ID', 'SKU', 'Descripción', 'Marca', 'Precio lista', 'Costo']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.sku,
            truncar(r.descripcion, 28),
            truncar(r.marca, 28),
            formatear_moneda(r.precio_lista),
            formatear_moneda(r.costo),
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Productos ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_productos_demo(n: int = 10, semilla: int = 13) -> List[Producto]:
    """Genera ``n`` registros de productos reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Producto] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["sku"] = sku_demo(rng)
        v["descripcion"] = f"{rng.choice(PRODUCTOS_DEMO)} {rng.choice(PRESENTACIONES_DEMO)}"
        v["marca"] = rng.choice(MARCAS_DEMO)
        v["categoria_clave"] = codigo_aleatorio(rng, 3, LETRAS)
        v["unidad"] = rng.choice(OPCIONES_PRODUCTO_UNIDAD)
        v["precio_lista"] = round(rng.uniform(9.5, 450), 2)
        v["costo"] = round(v["precio_lista"] * rng.uniform(0.55, 0.85), 2)
        v["codigo_barras"] = generar_ean13_demo(rng)
        v["perecedero"] = rng.random() < 0.3
        v["existencia_minima"] = rng.randint(2, 50)
        registros.append(Producto(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Sucursal  (Sucursales)
# ----------------------------------------------------------------------------

_PATRON_SUCURSAL_CLAVE = re.compile(r"^SUC\d{3}$")
OPCIONES_SUCURSAL_ESTADO = ('Jalisco', 'Guanajuato', 'Michoacán', 'Aguascalientes', 'Querétaro', 'Zacatecas')


@dataclass
class Sucursal:
    """Tienda física de la cadena."""

    id: int
    nombre: str
    clave: str
    ciudad: str
    estado: str
    codigo_postal: str
    telefono: str
    gerente: str
    metros_cuadrados: int
    fecha_apertura: str
    abierta_24h: bool = False

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 80:
            errores.append("nombre excede 80 caracteres")
        if not isinstance(self.clave, str) or not _PATRON_SUCURSAL_CLAVE.match(self.clave):
            errores.append("clave tiene un formato inválido")
        if not isinstance(self.ciudad, str) or not self.ciudad.strip():
            errores.append("ciudad es obligatorio")
        elif len(self.ciudad) > 60:
            errores.append("ciudad excede 60 caracteres")
        if self.estado not in OPCIONES_SUCURSAL_ESTADO:
            errores.append(f"estado debe ser uno de: {', '.join(OPCIONES_SUCURSAL_ESTADO)}")
        if not (isinstance(self.codigo_postal, str) and len(self.codigo_postal) == 5 and self.codigo_postal.isdigit()):
            errores.append("codigo_postal debe tener 5 dígitos")
        if not es_telefono_valido(self.telefono):
            errores.append("telefono debe tener 10 dígitos")
        if not isinstance(self.gerente, str) or not self.gerente.strip():
            errores.append("gerente es obligatorio")
        elif len(self.gerente) > 80:
            errores.append("gerente excede 80 caracteres")
        if not isinstance(self.metros_cuadrados, int) or isinstance(self.metros_cuadrados, bool) or not 50 <= self.metros_cuadrados <= 5000:
            errores.append("metros_cuadrados debe ser un entero entre 50 y 5000")
        if not es_fecha_iso(self.fecha_apertura):
            errores.append("fecha_apertura debe tener formato AAAA-MM-DD")
        if not isinstance(self.abierta_24h, bool):
            errores.append("abierta_24h debe ser booleano")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Sucursal":
        return cls(
            id=int(datos["id"]),
            nombre=str(datos["nombre"]),
            clave=str(datos["clave"]),
            ciudad=str(datos["ciudad"]),
            estado=str(datos["estado"]),
            codigo_postal=str(datos["codigo_postal"]),
            telefono=str(datos["telefono"]),
            gerente=str(datos["gerente"]),
            metros_cuadrados=int(datos["metros_cuadrados"]),
            fecha_apertura=str(datos["fecha_apertura"]),
            abierta_24h=a_booleano(datos.get("abierta_24h", False)),
        )


class RepositorioSucursales(RepositorioMemoria):
    """Repositorio en memoria de sucursales."""

    entidad = Sucursal
    nombre = "sucursales"
    CAMPOS_TEXTO = ('nombre', 'ciudad', 'gerente')

    def con_clave(self, valor: str) -> List[Sucursal]:
        return [r for r in self.listar() if r.clave == valor]

    def por_estado(self, valor: str) -> List[Sucursal]:
        """Registros cuyo campo estado es ``valor``."""
        if valor not in OPCIONES_SUCURSAL_ESTADO:
            raise ValueError(f"estado inválido: {valor!r}")
        return [r for r in self.listar() if r.estado == valor]

    def conteo_por_estado(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_SUCURSAL_ESTADO}
        for registro in self._items.values():
            conteo[registro.estado] += 1
        return conteo

    def con_metros_cuadrados_entre(self, minimo: int, maximo: int) -> List[Sucursal]:
        return [r for r in self.listar() if minimo <= r.metros_cuadrados <= maximo]

    def maximo_metros_cuadrados(self) -> Optional[int]:
        valores = [r.metros_cuadrados for r in self._items.values()]
        return max(valores) if valores else None

    def por_fecha_apertura_entre(self, inicio: str, fin: str) -> List[Sucursal]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_apertura and inicio <= r.fecha_apertura <= fin]

    def conteo_mensual_fecha_apertura(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_apertura:
                conteo[registro.fecha_apertura[:7]] += 1
        return dict(sorted(conteo.items()))

    def donde_abierta_24h(self, valor: bool = True) -> List[Sucursal]:
        return [r for r in self.listar() if r.abierta_24h is valor]

    def buscar_texto(self, termino: str) -> List[Sucursal]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_estado": self.conteo_por_estado(),
        }


def reporte_sucursales(repo: RepositorioSucursales, limite: int = 25) -> str:
    """Listado en texto plano de sucursales."""
    encabezados = ['ID', 'Nombre', 'Clave', 'Ciudad', 'Estado', 'Codigo postal']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            truncar(r.nombre, 28),
            r.clave,
            truncar(r.ciudad, 28),
            r.estado,
            r.codigo_postal,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Sucursales ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_sucursales_demo(n: int = 10, semilla: int = 14) -> List[Sucursal]:
    """Genera ``n`` registros de sucursales reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Sucursal] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["nombre"] = f"Sucursal {rng.choice(CIUDADES_DEMO)} {i}"
        v["clave"] = f"SUC{i:03d}"
        v["ciudad"] = rng.choice(CIUDADES_DEMO)
        v["estado"] = rng.choice(OPCIONES_SUCURSAL_ESTADO)
        v["codigo_postal"] = f"{rng.randint(44100, 45999):05d}"
        v["telefono"] = telefono_demo(rng)
        v["gerente"] = nombre_persona_demo(rng)
        v["metros_cuadrados"] = rng.randint(120, 2500)
        v["fecha_apertura"] = fecha_aleatoria_demo(rng, date(2005, 1, 1), date(2026, 6, 30))
        v["abierta_24h"] = rng.random() < 0.15
        registros.append(Sucursal(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Empleado  (Empleados)
# ----------------------------------------------------------------------------

OPCIONES_EMPLEADO_PUESTO = ('cajero', 'almacenista', 'supervisor', 'gerente', 'chofer', 'auxiliar')
_PATRON_EMPLEADO_SUCURSAL_CLAVE = re.compile(r"^SUC\d{3}$")
OPCIONES_EMPLEADO_TURNO = ('matutino', 'vespertino', 'nocturno', 'mixto')


@dataclass
class Empleado:
    """Colaborador de la cadena."""

    id: int
    nombre: str
    apellidos: str
    puesto: str
    sucursal_clave: str
    salario_mensual: float
    fecha_ingreso: str
    turno: str
    email: str = ''
    telefono: str = ''
    activo: bool = True

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 60:
            errores.append("nombre excede 60 caracteres")
        if not isinstance(self.apellidos, str) or not self.apellidos.strip():
            errores.append("apellidos es obligatorio")
        elif len(self.apellidos) > 80:
            errores.append("apellidos excede 80 caracteres")
        if self.puesto not in OPCIONES_EMPLEADO_PUESTO:
            errores.append(f"puesto debe ser uno de: {', '.join(OPCIONES_EMPLEADO_PUESTO)}")
        if not isinstance(self.sucursal_clave, str) or not _PATRON_EMPLEADO_SUCURSAL_CLAVE.match(self.sucursal_clave):
            errores.append("sucursal_clave tiene un formato inválido")
        if not isinstance(self.salario_mensual, (int, float)) or isinstance(self.salario_mensual, bool) or not 8475 <= self.salario_mensual <= 95_000:
            errores.append("salario_mensual debe estar entre 8475 y 95_000")
        if not es_fecha_iso(self.fecha_ingreso):
            errores.append("fecha_ingreso debe tener formato AAAA-MM-DD")
        if self.turno not in OPCIONES_EMPLEADO_TURNO:
            errores.append(f"turno debe ser uno de: {', '.join(OPCIONES_EMPLEADO_TURNO)}")
        if self.email and not es_email_valido(self.email):
            errores.append("email no es un correo válido")
        if self.telefono and not es_telefono_valido(self.telefono):
            errores.append("telefono debe tener 10 dígitos")
        if not isinstance(self.activo, bool):
            errores.append("activo debe ser booleano")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Empleado":
        return cls(
            id=int(datos["id"]),
            nombre=str(datos["nombre"]),
            apellidos=str(datos["apellidos"]),
            puesto=str(datos["puesto"]),
            sucursal_clave=str(datos["sucursal_clave"]),
            salario_mensual=float(datos["salario_mensual"]),
            fecha_ingreso=str(datos["fecha_ingreso"]),
            turno=str(datos["turno"]),
            email=str(datos.get("email", '')),
            telefono=str(datos.get("telefono", '')),
            activo=a_booleano(datos.get("activo", True)),
        )

    @property
    def nombre_completo(self) -> str:
        return capitalizar_nombre(f"{self.nombre} {self.apellidos}")

    def antiguedad_anios(self, al_dia: Optional[date] = None) -> int:
        return edad(date.fromisoformat(self.fecha_ingreso), al_dia or date.today())


class RepositorioEmpleados(RepositorioMemoria):
    """Repositorio en memoria de empleados."""

    entidad = Empleado
    nombre = "empleados"
    CAMPOS_TEXTO = ('nombre', 'apellidos')

    def por_puesto(self, valor: str) -> List[Empleado]:
        """Registros cuyo campo puesto es ``valor``."""
        if valor not in OPCIONES_EMPLEADO_PUESTO:
            raise ValueError(f"puesto inválido: {valor!r}")
        return [r for r in self.listar() if r.puesto == valor]

    def conteo_por_puesto(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_EMPLEADO_PUESTO}
        for registro in self._items.values():
            conteo[registro.puesto] += 1
        return conteo

    def con_sucursal_clave(self, valor: str) -> List[Empleado]:
        return [r for r in self.listar() if r.sucursal_clave == valor]

    def total_salario_mensual(self) -> float:
        return round(sum(r.salario_mensual for r in self._items.values()), 2)

    def promedio_salario_mensual(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.salario_mensual for r in self._items.values()), 2)

    def con_salario_mensual_entre(self, minimo: float, maximo: float) -> List[Empleado]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.salario_mensual <= maximo]

    def mayores_por_salario_mensual(self, n: int = 5) -> List[Empleado]:
        return sorted(self._items.values(), key=lambda r: (-r.salario_mensual, r.id))[:n]

    def por_fecha_ingreso_entre(self, inicio: str, fin: str) -> List[Empleado]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_ingreso and inicio <= r.fecha_ingreso <= fin]

    def conteo_mensual_fecha_ingreso(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_ingreso:
                conteo[registro.fecha_ingreso[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_turno(self, valor: str) -> List[Empleado]:
        """Registros cuyo campo turno es ``valor``."""
        if valor not in OPCIONES_EMPLEADO_TURNO:
            raise ValueError(f"turno inválido: {valor!r}")
        return [r for r in self.listar() if r.turno == valor]

    def conteo_por_turno(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_EMPLEADO_TURNO}
        for registro in self._items.values():
            conteo[registro.turno] += 1
        return conteo

    def donde_activo(self, valor: bool = True) -> List[Empleado]:
        return [r for r in self.listar() if r.activo is valor]

    def buscar_texto(self, termino: str) -> List[Empleado]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_puesto": self.conteo_por_puesto(),
            "total_salario_mensual": self.total_salario_mensual(),
            "por_turno": self.conteo_por_turno(),
        }

    def nomina_mensual(self) -> float:
        """Costo mensual de la plantilla activa."""
        return round(sum(e.salario_mensual for e in self._items.values() if e.activo), 2)


def reporte_empleados(repo: RepositorioEmpleados, limite: int = 25) -> str:
    """Listado en texto plano de empleados."""
    encabezados = ['ID', 'Nombre', 'Apellidos', 'Puesto', 'Sucursal', 'Salario']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            truncar(r.nombre, 28),
            truncar(r.apellidos, 28),
            r.puesto,
            r.sucursal_clave,
            formatear_moneda(r.salario_mensual),
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Empleados ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_empleados_demo(n: int = 10, semilla: int = 15) -> List[Empleado]:
    """Genera ``n`` registros de empleados reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Empleado] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["nombre"] = rng.choice(NOMBRES_DEMO)
        v["apellidos"] = f"{rng.choice(APELLIDOS_DEMO)} {rng.choice(APELLIDOS_DEMO)}"
        v["puesto"] = rng.choice(OPCIONES_EMPLEADO_PUESTO)
        v["sucursal_clave"] = f"SUC{rng.randint(1, 30):03d}"
        v["salario_mensual"] = round(rng.uniform(8500, 42_000), 2)
        v["fecha_ingreso"] = fecha_aleatoria_demo(rng, date(2010, 1, 1), date(2026, 10, 31))
        v["turno"] = rng.choice(OPCIONES_EMPLEADO_TURNO)
        v["email"] = email_demo(rng, v["nombre"])
        v["telefono"] = telefono_demo(rng)
        v["activo"] = rng.random() < 0.92
        registros.append(Empleado(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Cliente  (Clientes)
# ----------------------------------------------------------------------------

OPCIONES_CLIENTE_TIPO = ('mostrador', 'mayoreo', 'institucional', 'en_linea')


@dataclass
class Cliente:
    """Cliente registrado (programa de lealtad y crédito)."""

    id: int
    nombre: str
    rfc: str
    email: str
    tipo: str
    codigo_postal: str
    fecha_registro: str
    telefono: str = ''
    limite_credito: float = 0.0
    puntos: int = 0
    acepta_publicidad: bool = False

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 120:
            errores.append("nombre excede 120 caracteres")
        if not es_rfc_valido(self.rfc):
            errores.append("rfc no es un RFC válido")
        if not es_email_valido(self.email):
            errores.append("email no es un correo válido")
        if self.tipo not in OPCIONES_CLIENTE_TIPO:
            errores.append(f"tipo debe ser uno de: {', '.join(OPCIONES_CLIENTE_TIPO)}")
        if not (isinstance(self.codigo_postal, str) and len(self.codigo_postal) == 5 and self.codigo_postal.isdigit()):
            errores.append("codigo_postal debe tener 5 dígitos")
        if not es_fecha_iso(self.fecha_registro):
            errores.append("fecha_registro debe tener formato AAAA-MM-DD")
        if self.telefono and not es_telefono_valido(self.telefono):
            errores.append("telefono debe tener 10 dígitos")
        if not isinstance(self.limite_credito, (int, float)) or isinstance(self.limite_credito, bool) or not 0 <= self.limite_credito <= 500_000:
            errores.append("limite_credito debe estar entre 0 y 500_000")
        if not isinstance(self.puntos, int) or isinstance(self.puntos, bool) or not 0 <= self.puntos <= 1_000_000:
            errores.append("puntos debe ser un entero entre 0 y 1_000_000")
        if not isinstance(self.acepta_publicidad, bool):
            errores.append("acepta_publicidad debe ser booleano")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Cliente":
        return cls(
            id=int(datos["id"]),
            nombre=str(datos["nombre"]),
            rfc=str(datos["rfc"]),
            email=str(datos["email"]),
            tipo=str(datos["tipo"]),
            codigo_postal=str(datos["codigo_postal"]),
            fecha_registro=str(datos["fecha_registro"]),
            telefono=str(datos.get("telefono", '')),
            limite_credito=float(datos.get("limite_credito", 0.0)),
            puntos=int(datos.get("puntos", 0)),
            acepta_publicidad=a_booleano(datos.get("acepta_publicidad", False)),
        )

    @property
    def tipo_persona(self) -> str:
        return tipo_persona_por_rfc(self.rfc)

    def nivel_lealtad(self) -> str:
        if self.puntos >= 20_000:
            return "oro"
        if self.puntos >= 5_000:
            return "plata"
        return "bronce"


class RepositorioClientes(RepositorioMemoria):
    """Repositorio en memoria de clientes."""

    entidad = Cliente
    nombre = "clientes"
    CAMPOS_TEXTO = ('nombre',)

    def por_tipo(self, valor: str) -> List[Cliente]:
        """Registros cuyo campo tipo es ``valor``."""
        if valor not in OPCIONES_CLIENTE_TIPO:
            raise ValueError(f"tipo inválido: {valor!r}")
        return [r for r in self.listar() if r.tipo == valor]

    def conteo_por_tipo(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_CLIENTE_TIPO}
        for registro in self._items.values():
            conteo[registro.tipo] += 1
        return conteo

    def por_fecha_registro_entre(self, inicio: str, fin: str) -> List[Cliente]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_registro and inicio <= r.fecha_registro <= fin]

    def conteo_mensual_fecha_registro(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_registro:
                conteo[registro.fecha_registro[:7]] += 1
        return dict(sorted(conteo.items()))

    def total_limite_credito(self) -> float:
        return round(sum(r.limite_credito for r in self._items.values()), 2)

    def promedio_limite_credito(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.limite_credito for r in self._items.values()), 2)

    def con_limite_credito_entre(self, minimo: float, maximo: float) -> List[Cliente]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.limite_credito <= maximo]

    def mayores_por_limite_credito(self, n: int = 5) -> List[Cliente]:
        return sorted(self._items.values(), key=lambda r: (-r.limite_credito, r.id))[:n]

    def con_puntos_entre(self, minimo: int, maximo: int) -> List[Cliente]:
        return [r for r in self.listar() if minimo <= r.puntos <= maximo]

    def maximo_puntos(self) -> Optional[int]:
        valores = [r.puntos for r in self._items.values()]
        return max(valores) if valores else None

    def donde_acepta_publicidad(self, valor: bool = True) -> List[Cliente]:
        return [r for r in self.listar() if r.acepta_publicidad is valor]

    def buscar_texto(self, termino: str) -> List[Cliente]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_tipo": self.conteo_por_tipo(),
            "total_limite_credito": self.total_limite_credito(),
        }

    def por_nivel_lealtad(self) -> Dict[str, List[int]]:
        niveles: Dict[str, List[int]] = {"oro": [], "plata": [], "bronce": []}
        for cliente in self.listar():
            niveles[cliente.nivel_lealtad()].append(cliente.id)
        return niveles


def reporte_clientes(repo: RepositorioClientes, limite: int = 25) -> str:
    """Listado en texto plano de clientes."""
    encabezados = ['ID', 'Nombre', 'RFC', 'Correo', 'Tipo', 'Codigo postal']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            truncar(r.nombre, 28),
            r.rfc,
            r.email,
            r.tipo,
            r.codigo_postal,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Clientes ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_clientes_demo(n: int = 10, semilla: int = 16) -> List[Cliente]:
    """Genera ``n`` registros de clientes reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Cliente] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["nombre"] = nombre_persona_demo(rng) if rng.random() < 0.7 else razon_social_demo(rng)
        v["rfc"] = generar_rfc_demo(rng, moral=rng.random() < 0.3)
        v["email"] = email_demo(rng)
        v["tipo"] = rng.choice(OPCIONES_CLIENTE_TIPO)
        v["codigo_postal"] = f"{rng.randint(44100, 45999):05d}"
        v["fecha_registro"] = fecha_aleatoria_demo(rng)
        v["telefono"] = telefono_demo(rng)
        v["limite_credito"] = float(rng.choice((0, 0, 5000, 15_000, 50_000)))
        v["puntos"] = rng.randint(0, 25_000)
        v["acepta_publicidad"] = rng.random() < 0.4
        registros.append(Cliente(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Promocion  (Promociones)
# ----------------------------------------------------------------------------

OPCIONES_PROMOCION_TIPO = ('porcentaje', 'monto_fijo', 'nxm', 'regalo')
_PATRON_PROMOCION_CATEGORIA_CLAVE = re.compile(r"^[A-Z]{3}$")


@dataclass
class Promocion:
    """Promoción comercial con vigencia."""

    id: int
    nombre: str
    tipo: str
    valor: float
    fecha_inicio: str
    fecha_fin: str
    categoria_clave: str
    acumulable: bool = False
    compra_minima: float = 0.0

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 100:
            errores.append("nombre excede 100 caracteres")
        if self.tipo not in OPCIONES_PROMOCION_TIPO:
            errores.append(f"tipo debe ser uno de: {', '.join(OPCIONES_PROMOCION_TIPO)}")
        if not isinstance(self.valor, (int, float)) or isinstance(self.valor, bool) or not 0 <= self.valor <= 100:
            errores.append("valor debe estar entre 0 y 100")
        if not es_fecha_iso(self.fecha_inicio):
            errores.append("fecha_inicio debe tener formato AAAA-MM-DD")
        if not es_fecha_iso(self.fecha_fin):
            errores.append("fecha_fin debe tener formato AAAA-MM-DD")
        if not isinstance(self.categoria_clave, str) or not _PATRON_PROMOCION_CATEGORIA_CLAVE.match(self.categoria_clave):
            errores.append("categoria_clave tiene un formato inválido")
        if not isinstance(self.acumulable, bool):
            errores.append("acumulable debe ser booleano")
        if not isinstance(self.compra_minima, (int, float)) or isinstance(self.compra_minima, bool) or not 0 <= self.compra_minima <= 10_000:
            errores.append("compra_minima debe estar entre 0 y 10_000")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.fecha_fin > self.fecha_inicio:
                errores.append("fecha_fin no puede ser anterior a fecha_inicio")
            if self.tipo == "porcentaje" and self.valor > 90:
                errores.append("un descuento porcentual no puede exceder 90%")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Promocion":
        return cls(
            id=int(datos["id"]),
            nombre=str(datos["nombre"]),
            tipo=str(datos["tipo"]),
            valor=float(datos["valor"]),
            fecha_inicio=str(datos["fecha_inicio"]),
            fecha_fin=str(datos["fecha_fin"]),
            categoria_clave=str(datos["categoria_clave"]),
            acumulable=a_booleano(datos.get("acumulable", False)),
            compra_minima=float(datos.get("compra_minima", 0.0)),
        )

    def vigente_en(self, fecha_iso: str) -> bool:
        return self.fecha_inicio <= fecha_iso <= self.fecha_fin

    def duracion_dias(self) -> int:
        return (date.fromisoformat(self.fecha_fin) - date.fromisoformat(self.fecha_inicio)).days


class RepositorioPromociones(RepositorioMemoria):
    """Repositorio en memoria de promociones."""

    entidad = Promocion
    nombre = "promociones"
    CAMPOS_TEXTO = ('nombre',)

    def por_tipo(self, valor: str) -> List[Promocion]:
        """Registros cuyo campo tipo es ``valor``."""
        if valor not in OPCIONES_PROMOCION_TIPO:
            raise ValueError(f"tipo inválido: {valor!r}")
        return [r for r in self.listar() if r.tipo == valor]

    def conteo_por_tipo(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_PROMOCION_TIPO}
        for registro in self._items.values():
            conteo[registro.tipo] += 1
        return conteo

    def total_valor(self) -> float:
        return round(sum(r.valor for r in self._items.values()), 2)

    def promedio_valor(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.valor for r in self._items.values()), 2)

    def con_valor_entre(self, minimo: float, maximo: float) -> List[Promocion]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.valor <= maximo]

    def mayores_por_valor(self, n: int = 5) -> List[Promocion]:
        return sorted(self._items.values(), key=lambda r: (-r.valor, r.id))[:n]

    def por_fecha_inicio_entre(self, inicio: str, fin: str) -> List[Promocion]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_inicio and inicio <= r.fecha_inicio <= fin]

    def conteo_mensual_fecha_inicio(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_inicio:
                conteo[registro.fecha_inicio[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_fecha_fin_entre(self, inicio: str, fin: str) -> List[Promocion]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_fin and inicio <= r.fecha_fin <= fin]

    def conteo_mensual_fecha_fin(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_fin:
                conteo[registro.fecha_fin[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_categoria_clave(self, valor: str) -> List[Promocion]:
        return [r for r in self.listar() if r.categoria_clave == valor]

    def donde_acumulable(self, valor: bool = True) -> List[Promocion]:
        return [r for r in self.listar() if r.acumulable is valor]

    def total_compra_minima(self) -> float:
        return round(sum(r.compra_minima for r in self._items.values()), 2)

    def promedio_compra_minima(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.compra_minima for r in self._items.values()), 2)

    def con_compra_minima_entre(self, minimo: float, maximo: float) -> List[Promocion]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.compra_minima <= maximo]

    def mayores_por_compra_minima(self, n: int = 5) -> List[Promocion]:
        return sorted(self._items.values(), key=lambda r: (-r.compra_minima, r.id))[:n]

    def buscar_texto(self, termino: str) -> List[Promocion]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_tipo": self.conteo_por_tipo(),
            "total_compra_minima": self.total_compra_minima(),
        }

    def vigentes_en(self, fecha_iso: str) -> List[Promocion]:
        return [p for p in self.listar() if p.vigente_en(fecha_iso)]


def reporte_promociones(repo: RepositorioPromociones, limite: int = 25) -> str:
    """Listado en texto plano de promociones."""
    encabezados = ['ID', 'Nombre', 'Tipo', 'Valor', 'Inicio', 'Fin']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            truncar(r.nombre, 28),
            r.tipo,
            f"{r.valor:.2f}",
            r.fecha_inicio,
            r.fecha_fin,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Promociones ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_promociones_demo(n: int = 10, semilla: int = 17) -> List[Promocion]:
    """Genera ``n`` registros de promociones reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Promocion] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["nombre"] = f"Promo {rng.choice(PALABRAS_DEMO)} {rng.choice(NOMBRES_CATEGORIA_DEMO)}"
        v["tipo"] = rng.choice(OPCIONES_PROMOCION_TIPO)
        v["valor"] = round(rng.uniform(5, 60), 2)
        v["fecha_inicio"] = fecha_aleatoria_demo(rng, date(2025, 1, 1), date(2026, 10, 31))
        v["fecha_fin"] = sumar_dias_iso(v["fecha_inicio"], rng.randint(1, 45))
        v["categoria_clave"] = codigo_aleatorio(rng, 3, LETRAS)
        v["acumulable"] = rng.random() < 0.3
        v["compra_minima"] = float(rng.choice((0, 0, 100, 200, 500)))
        registros.append(Promocion(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Cupon  (Cupones)
# ----------------------------------------------------------------------------

_PATRON_CUPON_CODIGO = re.compile(r"^[A-Z0-9]{8}$")


@dataclass
class Cupon:
    """Cupón de descuento con límite de usos."""

    id: int
    codigo: str
    descuento_pct: float
    usos_maximos: int
    fecha_expiracion: str
    usos_actuales: int = 0
    activo: bool = True

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.codigo, str) or not _PATRON_CUPON_CODIGO.match(self.codigo):
            errores.append("codigo tiene un formato inválido")
        if not isinstance(self.descuento_pct, (int, float)) or isinstance(self.descuento_pct, bool) or not 1 <= self.descuento_pct <= 80:
            errores.append("descuento_pct debe estar entre 1 y 80")
        if not isinstance(self.usos_maximos, int) or isinstance(self.usos_maximos, bool) or not 1 <= self.usos_maximos <= 10_000:
            errores.append("usos_maximos debe ser un entero entre 1 y 10_000")
        if not es_fecha_iso(self.fecha_expiracion):
            errores.append("fecha_expiracion debe tener formato AAAA-MM-DD")
        if not isinstance(self.usos_actuales, int) or isinstance(self.usos_actuales, bool) or not 0 <= self.usos_actuales <= 10_000:
            errores.append("usos_actuales debe ser un entero entre 0 y 10_000")
        if not isinstance(self.activo, bool):
            errores.append("activo debe ser booleano")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.usos_actuales > self.usos_maximos:
                errores.append("usos_actuales excede usos_maximos")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Cupon":
        return cls(
            id=int(datos["id"]),
            codigo=str(datos["codigo"]),
            descuento_pct=float(datos["descuento_pct"]),
            usos_maximos=int(datos["usos_maximos"]),
            fecha_expiracion=str(datos["fecha_expiracion"]),
            usos_actuales=int(datos.get("usos_actuales", 0)),
            activo=a_booleano(datos.get("activo", True)),
        )

    def usos_restantes(self) -> int:
        return max(0, self.usos_maximos - self.usos_actuales)

    def puede_usarse(self, fecha_iso: str) -> bool:
        return self.activo and self.usos_restantes() > 0 and fecha_iso <= self.fecha_expiracion


class RepositorioCupones(RepositorioMemoria):
    """Repositorio en memoria de cupones."""

    entidad = Cupon
    nombre = "cupones"

    def con_codigo(self, valor: str) -> List[Cupon]:
        return [r for r in self.listar() if r.codigo == valor]

    def total_descuento_pct(self) -> float:
        return round(sum(r.descuento_pct for r in self._items.values()), 2)

    def promedio_descuento_pct(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.descuento_pct for r in self._items.values()), 2)

    def con_descuento_pct_entre(self, minimo: float, maximo: float) -> List[Cupon]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.descuento_pct <= maximo]

    def mayores_por_descuento_pct(self, n: int = 5) -> List[Cupon]:
        return sorted(self._items.values(), key=lambda r: (-r.descuento_pct, r.id))[:n]

    def con_usos_maximos_entre(self, minimo: int, maximo: int) -> List[Cupon]:
        return [r for r in self.listar() if minimo <= r.usos_maximos <= maximo]

    def maximo_usos_maximos(self) -> Optional[int]:
        valores = [r.usos_maximos for r in self._items.values()]
        return max(valores) if valores else None

    def por_fecha_expiracion_entre(self, inicio: str, fin: str) -> List[Cupon]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_expiracion and inicio <= r.fecha_expiracion <= fin]

    def conteo_mensual_fecha_expiracion(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_expiracion:
                conteo[registro.fecha_expiracion[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_usos_actuales_entre(self, minimo: int, maximo: int) -> List[Cupon]:
        return [r for r in self.listar() if minimo <= r.usos_actuales <= maximo]

    def maximo_usos_actuales(self) -> Optional[int]:
        valores = [r.usos_actuales for r in self._items.values()]
        return max(valores) if valores else None

    def donde_activo(self, valor: bool = True) -> List[Cupon]:
        return [r for r in self.listar() if r.activo is valor]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
        }


def reporte_cupones(repo: RepositorioCupones, limite: int = 25) -> str:
    """Listado en texto plano de cupones."""
    encabezados = ['ID', 'Código', 'Descuento %', 'Usos máx.', 'Expira', 'Usos']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.codigo,
            f"{r.descuento_pct:.2f}",
            r.usos_maximos,
            r.fecha_expiracion,
            r.usos_actuales,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Cupones ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_cupones_demo(n: int = 10, semilla: int = 18) -> List[Cupon]:
    """Genera ``n`` registros de cupones reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Cupon] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["codigo"] = codigo_aleatorio(rng, 8)
        v["descuento_pct"] = float(rng.choice((5, 10, 15, 20, 25, 30)))
        v["usos_maximos"] = rng.randint(1, 500)
        v["fecha_expiracion"] = fecha_aleatoria_demo(rng)
        v["usos_actuales"] = rng.randint(0, v["usos_maximos"])
        v["activo"] = rng.random() < 0.85
        registros.append(Cupon(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Pedido  (Órdenes de compra)
# ----------------------------------------------------------------------------

_PATRON_PEDIDO_FOLIO = re.compile(r"^OC-\d{6}$")
_PATRON_PEDIDO_SUCURSAL_CLAVE = re.compile(r"^SUC\d{3}$")
OPCIONES_PEDIDO_ESTATUS = ('borrador', 'enviado', 'parcial', 'recibido', 'cancelado')


@dataclass
class Pedido:
    """Orden de compra emitida a un proveedor."""

    id: int
    folio: str
    proveedor_id: int
    sucursal_clave: str
    fecha_pedido: str
    fecha_entrega_estimada: str
    estatus: str
    subtotal: float
    iva: float
    total: float
    observaciones: str = ''

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.folio, str) or not _PATRON_PEDIDO_FOLIO.match(self.folio):
            errores.append("folio tiene un formato inválido")
        if not isinstance(self.proveedor_id, int) or isinstance(self.proveedor_id, bool) or not 1 <= self.proveedor_id <= 99_999:
            errores.append("proveedor_id debe ser un entero entre 1 y 99_999")
        if not isinstance(self.sucursal_clave, str) or not _PATRON_PEDIDO_SUCURSAL_CLAVE.match(self.sucursal_clave):
            errores.append("sucursal_clave tiene un formato inválido")
        if not es_fecha_iso(self.fecha_pedido):
            errores.append("fecha_pedido debe tener formato AAAA-MM-DD")
        if not es_fecha_iso(self.fecha_entrega_estimada):
            errores.append("fecha_entrega_estimada debe tener formato AAAA-MM-DD")
        if self.estatus not in OPCIONES_PEDIDO_ESTATUS:
            errores.append(f"estatus debe ser uno de: {', '.join(OPCIONES_PEDIDO_ESTATUS)}")
        if not isinstance(self.subtotal, (int, float)) or isinstance(self.subtotal, bool) or not 0 <= self.subtotal <= 5_000_000:
            errores.append("subtotal debe estar entre 0 y 5_000_000")
        if not isinstance(self.iva, (int, float)) or isinstance(self.iva, bool) or not 0 <= self.iva <= 800_000:
            errores.append("iva debe estar entre 0 y 800_000")
        if not isinstance(self.total, (int, float)) or isinstance(self.total, bool) or not 0 <= self.total <= 5_800_000:
            errores.append("total debe estar entre 0 y 5_800_000")
        if not isinstance(self.observaciones, str):
            errores.append("observaciones debe ser texto")
        elif len(self.observaciones) > 250:
            errores.append("observaciones excede 250 caracteres")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.fecha_entrega_estimada < self.fecha_pedido:
                errores.append("la entrega estimada no puede ser anterior al pedido")
            if abs(self.total - (self.subtotal + self.iva)) > 0.01:
                errores.append("el total no coincide con subtotal + iva")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Pedido":
        return cls(
            id=int(datos["id"]),
            folio=str(datos["folio"]),
            proveedor_id=int(datos["proveedor_id"]),
            sucursal_clave=str(datos["sucursal_clave"]),
            fecha_pedido=str(datos["fecha_pedido"]),
            fecha_entrega_estimada=str(datos["fecha_entrega_estimada"]),
            estatus=str(datos["estatus"]),
            subtotal=float(datos["subtotal"]),
            iva=float(datos["iva"]),
            total=float(datos["total"]),
            observaciones=str(datos.get("observaciones", '')),
        )


class RepositorioPedidos(RepositorioMemoria):
    """Repositorio en memoria de órdenes de compra."""

    entidad = Pedido
    nombre = "pedidos"
    CAMPOS_TEXTO = ('observaciones',)

    def con_folio(self, valor: str) -> List[Pedido]:
        return [r for r in self.listar() if r.folio == valor]

    def con_proveedor_id_entre(self, minimo: int, maximo: int) -> List[Pedido]:
        return [r for r in self.listar() if minimo <= r.proveedor_id <= maximo]

    def maximo_proveedor_id(self) -> Optional[int]:
        valores = [r.proveedor_id for r in self._items.values()]
        return max(valores) if valores else None

    def con_sucursal_clave(self, valor: str) -> List[Pedido]:
        return [r for r in self.listar() if r.sucursal_clave == valor]

    def por_fecha_pedido_entre(self, inicio: str, fin: str) -> List[Pedido]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_pedido and inicio <= r.fecha_pedido <= fin]

    def conteo_mensual_fecha_pedido(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_pedido:
                conteo[registro.fecha_pedido[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_fecha_entrega_estimada_entre(self, inicio: str, fin: str) -> List[Pedido]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_entrega_estimada and inicio <= r.fecha_entrega_estimada <= fin]

    def conteo_mensual_fecha_entrega_estimada(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_entrega_estimada:
                conteo[registro.fecha_entrega_estimada[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_estatus(self, valor: str) -> List[Pedido]:
        """Registros cuyo campo estatus es ``valor``."""
        if valor not in OPCIONES_PEDIDO_ESTATUS:
            raise ValueError(f"estatus inválido: {valor!r}")
        return [r for r in self.listar() if r.estatus == valor]

    def conteo_por_estatus(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_PEDIDO_ESTATUS}
        for registro in self._items.values():
            conteo[registro.estatus] += 1
        return conteo

    def total_subtotal(self) -> float:
        return round(sum(r.subtotal for r in self._items.values()), 2)

    def promedio_subtotal(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.subtotal for r in self._items.values()), 2)

    def con_subtotal_entre(self, minimo: float, maximo: float) -> List[Pedido]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.subtotal <= maximo]

    def mayores_por_subtotal(self, n: int = 5) -> List[Pedido]:
        return sorted(self._items.values(), key=lambda r: (-r.subtotal, r.id))[:n]

    def total_iva(self) -> float:
        return round(sum(r.iva for r in self._items.values()), 2)

    def promedio_iva(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.iva for r in self._items.values()), 2)

    def con_iva_entre(self, minimo: float, maximo: float) -> List[Pedido]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.iva <= maximo]

    def mayores_por_iva(self, n: int = 5) -> List[Pedido]:
        return sorted(self._items.values(), key=lambda r: (-r.iva, r.id))[:n]

    def total_total(self) -> float:
        return round(sum(r.total for r in self._items.values()), 2)

    def promedio_total(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.total for r in self._items.values()), 2)

    def con_total_entre(self, minimo: float, maximo: float) -> List[Pedido]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.total <= maximo]

    def mayores_por_total(self, n: int = 5) -> List[Pedido]:
        return sorted(self._items.values(), key=lambda r: (-r.total, r.id))[:n]

    def buscar_texto(self, termino: str) -> List[Pedido]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_estatus": self.conteo_por_estatus(),
            "total_subtotal": self.total_subtotal(),
            "total_iva": self.total_iva(),
            "total_total": self.total_total(),
        }

    def pendientes_de_recibir(self) -> List[Pedido]:
        return [p for p in self.listar() if p.estatus in ("enviado", "parcial")]

    def atrasados(self, hoy_iso: str) -> List[Pedido]:
        return [p for p in self.pendientes_de_recibir() if p.fecha_entrega_estimada < hoy_iso]


def reporte_pedidos(repo: RepositorioPedidos, limite: int = 25) -> str:
    """Listado en texto plano de órdenes de compra."""
    encabezados = ['ID', 'Folio', 'Proveedor', 'Sucursal clave', 'Fecha', 'Fecha entrega estimada']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.folio,
            r.proveedor_id,
            r.sucursal_clave,
            r.fecha_pedido,
            r.fecha_entrega_estimada,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Órdenes de compra ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_pedidos_demo(n: int = 10, semilla: int = 19) -> List[Pedido]:
    """Genera ``n`` registros de órdenes de compra reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Pedido] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["folio"] = f"OC-{rng.randint(1, 999_999):06d}"
        v["proveedor_id"] = rng.randint(1, 300)
        v["sucursal_clave"] = f"SUC{rng.randint(1, 30):03d}"
        v["fecha_pedido"] = fecha_aleatoria_demo(rng)
        v["fecha_entrega_estimada"] = sumar_dias_iso(v["fecha_pedido"], rng.randint(1, 21))
        v["estatus"] = rng.choice(OPCIONES_PEDIDO_ESTATUS)
        v["subtotal"] = round(rng.uniform(1500, 250_000), 2)
        v["iva"] = round(v["subtotal"] * TASA_IVA, 2)
        v["total"] = round(v["subtotal"] + v["iva"], 2)
        v["observaciones"] = frase_demo(rng, 5) if rng.random() < 0.4 else ""
        registros.append(Pedido(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Envio  (Envíos)
# ----------------------------------------------------------------------------

_PATRON_ENVIO_GUIA = re.compile(r"^ENV\d{8}$")
_PATRON_ENVIO_PEDIDO_FOLIO = re.compile(r"^OC-\d{6}$")
OPCIONES_ENVIO_TRANSPORTISTA = ('propio', 'estafeta', 'dhl', 'paquetexpress', 'fedex')


@dataclass
class Envio:
    """Envío de mercancía entre CEDIS y sucursales."""

    id: int
    guia: str
    pedido_folio: str
    transportista: str
    peso_kg: float
    costo: float
    fecha_salida: str
    destino_cp: str
    entregado: bool = False

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.guia, str) or not _PATRON_ENVIO_GUIA.match(self.guia):
            errores.append("guia tiene un formato inválido")
        if not isinstance(self.pedido_folio, str) or not _PATRON_ENVIO_PEDIDO_FOLIO.match(self.pedido_folio):
            errores.append("pedido_folio tiene un formato inválido")
        if self.transportista not in OPCIONES_ENVIO_TRANSPORTISTA:
            errores.append(f"transportista debe ser uno de: {', '.join(OPCIONES_ENVIO_TRANSPORTISTA)}")
        if not isinstance(self.peso_kg, (int, float)) or isinstance(self.peso_kg, bool) or not 0.1 <= self.peso_kg <= 30_000:
            errores.append("peso_kg debe estar entre 0.1 y 30_000")
        if not isinstance(self.costo, (int, float)) or isinstance(self.costo, bool) or not 0 <= self.costo <= 100_000:
            errores.append("costo debe estar entre 0 y 100_000")
        if not es_fecha_iso(self.fecha_salida):
            errores.append("fecha_salida debe tener formato AAAA-MM-DD")
        if not (isinstance(self.destino_cp, str) and len(self.destino_cp) == 5 and self.destino_cp.isdigit()):
            errores.append("destino_cp debe tener 5 dígitos")
        if not isinstance(self.entregado, bool):
            errores.append("entregado debe ser booleano")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Envio":
        return cls(
            id=int(datos["id"]),
            guia=str(datos["guia"]),
            pedido_folio=str(datos["pedido_folio"]),
            transportista=str(datos["transportista"]),
            peso_kg=float(datos["peso_kg"]),
            costo=float(datos["costo"]),
            fecha_salida=str(datos["fecha_salida"]),
            destino_cp=str(datos["destino_cp"]),
            entregado=a_booleano(datos.get("entregado", False)),
        )

    def costo_por_kg(self) -> float:
        return round(self.costo / self.peso_kg, 2) if self.peso_kg else 0.0


class RepositorioEnvios(RepositorioMemoria):
    """Repositorio en memoria de envíos."""

    entidad = Envio
    nombre = "envios"

    def con_guia(self, valor: str) -> List[Envio]:
        return [r for r in self.listar() if r.guia == valor]

    def con_pedido_folio(self, valor: str) -> List[Envio]:
        return [r for r in self.listar() if r.pedido_folio == valor]

    def por_transportista(self, valor: str) -> List[Envio]:
        """Registros cuyo campo transportista es ``valor``."""
        if valor not in OPCIONES_ENVIO_TRANSPORTISTA:
            raise ValueError(f"transportista inválido: {valor!r}")
        return [r for r in self.listar() if r.transportista == valor]

    def conteo_por_transportista(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_ENVIO_TRANSPORTISTA}
        for registro in self._items.values():
            conteo[registro.transportista] += 1
        return conteo

    def total_peso_kg(self) -> float:
        return round(sum(r.peso_kg for r in self._items.values()), 2)

    def promedio_peso_kg(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.peso_kg for r in self._items.values()), 2)

    def con_peso_kg_entre(self, minimo: float, maximo: float) -> List[Envio]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.peso_kg <= maximo]

    def mayores_por_peso_kg(self, n: int = 5) -> List[Envio]:
        return sorted(self._items.values(), key=lambda r: (-r.peso_kg, r.id))[:n]

    def total_costo(self) -> float:
        return round(sum(r.costo for r in self._items.values()), 2)

    def promedio_costo(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.costo for r in self._items.values()), 2)

    def con_costo_entre(self, minimo: float, maximo: float) -> List[Envio]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.costo <= maximo]

    def mayores_por_costo(self, n: int = 5) -> List[Envio]:
        return sorted(self._items.values(), key=lambda r: (-r.costo, r.id))[:n]

    def por_fecha_salida_entre(self, inicio: str, fin: str) -> List[Envio]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_salida and inicio <= r.fecha_salida <= fin]

    def conteo_mensual_fecha_salida(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_salida:
                conteo[registro.fecha_salida[:7]] += 1
        return dict(sorted(conteo.items()))

    def donde_entregado(self, valor: bool = True) -> List[Envio]:
        return [r for r in self.listar() if r.entregado is valor]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_transportista": self.conteo_por_transportista(),
            "total_costo": self.total_costo(),
        }


def reporte_envios(repo: RepositorioEnvios, limite: int = 25) -> str:
    """Listado en texto plano de envíos."""
    encabezados = ['ID', 'Guía', 'Pedido', 'Transportista', 'Peso kg', 'Costo']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.guia,
            r.pedido_folio,
            r.transportista,
            f"{r.peso_kg:.2f}",
            formatear_moneda(r.costo),
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Envíos ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_envios_demo(n: int = 10, semilla: int = 20) -> List[Envio]:
    """Genera ``n`` registros de envíos reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Envio] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["guia"] = f"ENV{rng.randint(0, 99_999_999):08d}"
        v["pedido_folio"] = f"OC-{rng.randint(1, 999_999):06d}"
        v["transportista"] = rng.choice(OPCIONES_ENVIO_TRANSPORTISTA)
        v["peso_kg"] = round(rng.uniform(0.5, 3500), 2)
        v["costo"] = round(rng.uniform(150, 12_000), 2)
        v["fecha_salida"] = fecha_aleatoria_demo(rng)
        v["destino_cp"] = f"{rng.randint(44100, 45999):05d}"
        v["entregado"] = rng.random() < 0.6
        registros.append(Envio(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Devolucion  (Devoluciones)
# ----------------------------------------------------------------------------

_PATRON_DEVOLUCION_FOLIO_VENTA = re.compile(r"^V-\d{6}$")
_PATRON_DEVOLUCION_SKU = re.compile(r"^[A-Z]{3}-\d{5}$")
OPCIONES_DEVOLUCION_MOTIVO = ('caducado', 'dañado', 'equivocado', 'garantia', 'otro')


@dataclass
class Devolucion:
    """Devolución de mercancía por parte de un cliente."""

    id: int
    folio_venta: str
    sku: str
    cantidad: int
    motivo: str
    monto: float
    fecha: str
    autorizada_por: str = ''
    reingresa_inventario: bool = False

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.folio_venta, str) or not _PATRON_DEVOLUCION_FOLIO_VENTA.match(self.folio_venta):
            errores.append("folio_venta tiene un formato inválido")
        if not isinstance(self.sku, str) or not _PATRON_DEVOLUCION_SKU.match(self.sku):
            errores.append("sku tiene un formato inválido")
        if not isinstance(self.cantidad, int) or isinstance(self.cantidad, bool) or not 1 <= self.cantidad <= 1000:
            errores.append("cantidad debe ser un entero entre 1 y 1000")
        if self.motivo not in OPCIONES_DEVOLUCION_MOTIVO:
            errores.append(f"motivo debe ser uno de: {', '.join(OPCIONES_DEVOLUCION_MOTIVO)}")
        if not isinstance(self.monto, (int, float)) or isinstance(self.monto, bool) or not 0 <= self.monto <= 100_000:
            errores.append("monto debe estar entre 0 y 100_000")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if not isinstance(self.autorizada_por, str):
            errores.append("autorizada_por debe ser texto")
        elif len(self.autorizada_por) > 80:
            errores.append("autorizada_por excede 80 caracteres")
        if not isinstance(self.reingresa_inventario, bool):
            errores.append("reingresa_inventario debe ser booleano")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.reingresa_inventario and self.motivo in ("caducado", "dañado"):
                errores.append("la mercancía caducada o dañada no puede reingresar al inventario")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Devolucion":
        return cls(
            id=int(datos["id"]),
            folio_venta=str(datos["folio_venta"]),
            sku=str(datos["sku"]),
            cantidad=int(datos["cantidad"]),
            motivo=str(datos["motivo"]),
            monto=float(datos["monto"]),
            fecha=str(datos["fecha"]),
            autorizada_por=str(datos.get("autorizada_por", '')),
            reingresa_inventario=a_booleano(datos.get("reingresa_inventario", False)),
        )


class RepositorioDevoluciones(RepositorioMemoria):
    """Repositorio en memoria de devoluciones."""

    entidad = Devolucion
    nombre = "devoluciones"
    CAMPOS_TEXTO = ('autorizada_por',)

    def con_folio_venta(self, valor: str) -> List[Devolucion]:
        return [r for r in self.listar() if r.folio_venta == valor]

    def con_sku(self, valor: str) -> List[Devolucion]:
        return [r for r in self.listar() if r.sku == valor]

    def con_cantidad_entre(self, minimo: int, maximo: int) -> List[Devolucion]:
        return [r for r in self.listar() if minimo <= r.cantidad <= maximo]

    def maximo_cantidad(self) -> Optional[int]:
        valores = [r.cantidad for r in self._items.values()]
        return max(valores) if valores else None

    def por_motivo(self, valor: str) -> List[Devolucion]:
        """Registros cuyo campo motivo es ``valor``."""
        if valor not in OPCIONES_DEVOLUCION_MOTIVO:
            raise ValueError(f"motivo inválido: {valor!r}")
        return [r for r in self.listar() if r.motivo == valor]

    def conteo_por_motivo(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_DEVOLUCION_MOTIVO}
        for registro in self._items.values():
            conteo[registro.motivo] += 1
        return conteo

    def total_monto(self) -> float:
        return round(sum(r.monto for r in self._items.values()), 2)

    def promedio_monto(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.monto for r in self._items.values()), 2)

    def con_monto_entre(self, minimo: float, maximo: float) -> List[Devolucion]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.monto <= maximo]

    def mayores_por_monto(self, n: int = 5) -> List[Devolucion]:
        return sorted(self._items.values(), key=lambda r: (-r.monto, r.id))[:n]

    def por_fecha_entre(self, inicio: str, fin: str) -> List[Devolucion]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def donde_reingresa_inventario(self, valor: bool = True) -> List[Devolucion]:
        return [r for r in self.listar() if r.reingresa_inventario is valor]

    def buscar_texto(self, termino: str) -> List[Devolucion]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_motivo": self.conteo_por_motivo(),
            "total_monto": self.total_monto(),
        }


def reporte_devoluciones(repo: RepositorioDevoluciones, limite: int = 25) -> str:
    """Listado en texto plano de devoluciones."""
    encabezados = ['ID', 'Venta', 'SKU', 'Cantidad', 'Motivo', 'Monto']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.folio_venta,
            r.sku,
            r.cantidad,
            r.motivo,
            formatear_moneda(r.monto),
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Devoluciones ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_devoluciones_demo(n: int = 10, semilla: int = 21) -> List[Devolucion]:
    """Genera ``n`` registros de devoluciones reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Devolucion] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["folio_venta"] = f"V-{rng.randint(1, 999_999):06d}"
        v["sku"] = sku_demo(rng)
        v["cantidad"] = rng.randint(1, 12)
        v["motivo"] = rng.choice(OPCIONES_DEVOLUCION_MOTIVO)
        v["monto"] = round(rng.uniform(10, 2500), 2)
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["autorizada_por"] = nombre_persona_demo(rng) if rng.random() < 0.6 else ""
        v["reingresa_inventario"] = v["motivo"] not in ("caducado", "dañado") and rng.random() < 0.5
        registros.append(Devolucion(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Almacen  (Almacenes)
# ----------------------------------------------------------------------------

_PATRON_ALMACEN_CLAVE = re.compile(r"^ALM\d{2}$")
_PATRON_ALMACEN_SUCURSAL_CLAVE = re.compile(r"^SUC\d{3}$")


@dataclass
class Almacen:
    """Almacén o bodega asociado a una sucursal."""

    id: int
    clave: str
    nombre: str
    sucursal_clave: str
    capacidad_m3: float
    ocupacion_pct: float
    refrigerado: bool
    responsable: str = ''

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.clave, str) or not _PATRON_ALMACEN_CLAVE.match(self.clave):
            errores.append("clave tiene un formato inválido")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 80:
            errores.append("nombre excede 80 caracteres")
        if not isinstance(self.sucursal_clave, str) or not _PATRON_ALMACEN_SUCURSAL_CLAVE.match(self.sucursal_clave):
            errores.append("sucursal_clave tiene un formato inválido")
        if not isinstance(self.capacidad_m3, (int, float)) or isinstance(self.capacidad_m3, bool) or not 10 <= self.capacidad_m3 <= 100_000:
            errores.append("capacidad_m3 debe estar entre 10 y 100_000")
        if not isinstance(self.ocupacion_pct, (int, float)) or isinstance(self.ocupacion_pct, bool) or not 0 <= self.ocupacion_pct <= 100:
            errores.append("ocupacion_pct debe estar entre 0 y 100")
        if not isinstance(self.refrigerado, bool):
            errores.append("refrigerado debe ser booleano")
        if not isinstance(self.responsable, str):
            errores.append("responsable debe ser texto")
        elif len(self.responsable) > 80:
            errores.append("responsable excede 80 caracteres")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Almacen":
        return cls(
            id=int(datos["id"]),
            clave=str(datos["clave"]),
            nombre=str(datos["nombre"]),
            sucursal_clave=str(datos["sucursal_clave"]),
            capacidad_m3=float(datos["capacidad_m3"]),
            ocupacion_pct=float(datos["ocupacion_pct"]),
            refrigerado=a_booleano(datos["refrigerado"]),
            responsable=str(datos.get("responsable", '')),
        )

    def espacio_disponible_m3(self) -> float:
        return round(self.capacidad_m3 * (1 - self.ocupacion_pct / 100), 2)


class RepositorioAlmacenes(RepositorioMemoria):
    """Repositorio en memoria de almacenes."""

    entidad = Almacen
    nombre = "almacenes"
    CAMPOS_TEXTO = ('nombre', 'responsable')

    def con_clave(self, valor: str) -> List[Almacen]:
        return [r for r in self.listar() if r.clave == valor]

    def con_sucursal_clave(self, valor: str) -> List[Almacen]:
        return [r for r in self.listar() if r.sucursal_clave == valor]

    def total_capacidad_m3(self) -> float:
        return round(sum(r.capacidad_m3 for r in self._items.values()), 2)

    def promedio_capacidad_m3(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.capacidad_m3 for r in self._items.values()), 2)

    def con_capacidad_m3_entre(self, minimo: float, maximo: float) -> List[Almacen]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.capacidad_m3 <= maximo]

    def mayores_por_capacidad_m3(self, n: int = 5) -> List[Almacen]:
        return sorted(self._items.values(), key=lambda r: (-r.capacidad_m3, r.id))[:n]

    def total_ocupacion_pct(self) -> float:
        return round(sum(r.ocupacion_pct for r in self._items.values()), 2)

    def promedio_ocupacion_pct(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.ocupacion_pct for r in self._items.values()), 2)

    def con_ocupacion_pct_entre(self, minimo: float, maximo: float) -> List[Almacen]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.ocupacion_pct <= maximo]

    def mayores_por_ocupacion_pct(self, n: int = 5) -> List[Almacen]:
        return sorted(self._items.values(), key=lambda r: (-r.ocupacion_pct, r.id))[:n]

    def donde_refrigerado(self, valor: bool = True) -> List[Almacen]:
        return [r for r in self.listar() if r.refrigerado is valor]

    def buscar_texto(self, termino: str) -> List[Almacen]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
        }

    def saturados(self, umbral: float = 90.0) -> List[Almacen]:
        return [a for a in self.listar() if a.ocupacion_pct >= umbral]


def reporte_almacenes(repo: RepositorioAlmacenes, limite: int = 25) -> str:
    """Listado en texto plano de almacenes."""
    encabezados = ['ID', 'Clave', 'Nombre', 'Sucursal', 'Capacidad m3', 'Ocupación %']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.clave,
            truncar(r.nombre, 28),
            r.sucursal_clave,
            f"{r.capacidad_m3:.2f}",
            f"{r.ocupacion_pct:.2f}",
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Almacenes ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_almacenes_demo(n: int = 10, semilla: int = 22) -> List[Almacen]:
    """Genera ``n`` registros de almacenes reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Almacen] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["clave"] = f"ALM{i:02d}"
        v["nombre"] = f"Almacén {rng.choice(CIUDADES_DEMO)}"
        v["sucursal_clave"] = f"SUC{rng.randint(1, 30):03d}"
        v["capacidad_m3"] = round(rng.uniform(80, 6000), 2)
        v["ocupacion_pct"] = round(rng.uniform(15, 98), 2)
        v["refrigerado"] = rng.random() < 0.25
        v["responsable"] = nombre_persona_demo(rng)
        registros.append(Almacen(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Vehiculo  (Vehículos)
# ----------------------------------------------------------------------------

_PATRON_VEHICULO_PLACAS = re.compile(r"^[A-Z]{3}-\d{3}-[A-Z]$")
OPCIONES_VEHICULO_TIPO = ('camioneta', 'torton', 'rabon', 'motocicleta', 'sedan')


@dataclass
class Vehiculo:
    """Unidad de la flotilla de reparto."""

    id: int
    placas: str
    marca: str
    modelo: str
    anio: int
    tipo: str
    capacidad_kg: int
    kilometraje: int = 0
    en_servicio: bool = True
    fecha_ultimo_servicio: str = ''

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.placas, str) or not _PATRON_VEHICULO_PLACAS.match(self.placas):
            errores.append("placas tiene un formato inválido")
        if not isinstance(self.marca, str) or not self.marca.strip():
            errores.append("marca es obligatorio")
        elif len(self.marca) > 40:
            errores.append("marca excede 40 caracteres")
        if not isinstance(self.modelo, str) or not self.modelo.strip():
            errores.append("modelo es obligatorio")
        elif len(self.modelo) > 40:
            errores.append("modelo excede 40 caracteres")
        if not isinstance(self.anio, int) or isinstance(self.anio, bool) or not 2005 <= self.anio <= 2027:
            errores.append("anio debe ser un entero entre 2005 y 2027")
        if self.tipo not in OPCIONES_VEHICULO_TIPO:
            errores.append(f"tipo debe ser uno de: {', '.join(OPCIONES_VEHICULO_TIPO)}")
        if not isinstance(self.capacidad_kg, int) or isinstance(self.capacidad_kg, bool) or not 50 <= self.capacidad_kg <= 20_000:
            errores.append("capacidad_kg debe ser un entero entre 50 y 20_000")
        if not isinstance(self.kilometraje, int) or isinstance(self.kilometraje, bool) or not 0 <= self.kilometraje <= 900_000:
            errores.append("kilometraje debe ser un entero entre 0 y 900_000")
        if not isinstance(self.en_servicio, bool):
            errores.append("en_servicio debe ser booleano")
        if self.fecha_ultimo_servicio and not es_fecha_iso(self.fecha_ultimo_servicio):
            errores.append("fecha_ultimo_servicio debe tener formato AAAA-MM-DD")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Vehiculo":
        return cls(
            id=int(datos["id"]),
            placas=str(datos["placas"]),
            marca=str(datos["marca"]),
            modelo=str(datos["modelo"]),
            anio=int(datos["anio"]),
            tipo=str(datos["tipo"]),
            capacidad_kg=int(datos["capacidad_kg"]),
            kilometraje=int(datos.get("kilometraje", 0)),
            en_servicio=a_booleano(datos.get("en_servicio", True)),
            fecha_ultimo_servicio=str(datos.get("fecha_ultimo_servicio", '')),
        )

    def antiguedad(self, anio_actual: int = 2026) -> int:
        return max(0, anio_actual - self.anio)


class RepositorioVehiculos(RepositorioMemoria):
    """Repositorio en memoria de vehículos."""

    entidad = Vehiculo
    nombre = "vehiculos"
    CAMPOS_TEXTO = ('marca', 'modelo')

    def con_placas(self, valor: str) -> List[Vehiculo]:
        return [r for r in self.listar() if r.placas == valor]

    def con_anio_entre(self, minimo: int, maximo: int) -> List[Vehiculo]:
        return [r for r in self.listar() if minimo <= r.anio <= maximo]

    def maximo_anio(self) -> Optional[int]:
        valores = [r.anio for r in self._items.values()]
        return max(valores) if valores else None

    def por_tipo(self, valor: str) -> List[Vehiculo]:
        """Registros cuyo campo tipo es ``valor``."""
        if valor not in OPCIONES_VEHICULO_TIPO:
            raise ValueError(f"tipo inválido: {valor!r}")
        return [r for r in self.listar() if r.tipo == valor]

    def conteo_por_tipo(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_VEHICULO_TIPO}
        for registro in self._items.values():
            conteo[registro.tipo] += 1
        return conteo

    def con_capacidad_kg_entre(self, minimo: int, maximo: int) -> List[Vehiculo]:
        return [r for r in self.listar() if minimo <= r.capacidad_kg <= maximo]

    def maximo_capacidad_kg(self) -> Optional[int]:
        valores = [r.capacidad_kg for r in self._items.values()]
        return max(valores) if valores else None

    def con_kilometraje_entre(self, minimo: int, maximo: int) -> List[Vehiculo]:
        return [r for r in self.listar() if minimo <= r.kilometraje <= maximo]

    def maximo_kilometraje(self) -> Optional[int]:
        valores = [r.kilometraje for r in self._items.values()]
        return max(valores) if valores else None

    def donde_en_servicio(self, valor: bool = True) -> List[Vehiculo]:
        return [r for r in self.listar() if r.en_servicio is valor]

    def por_fecha_ultimo_servicio_entre(self, inicio: str, fin: str) -> List[Vehiculo]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha_ultimo_servicio and inicio <= r.fecha_ultimo_servicio <= fin]

    def conteo_mensual_fecha_ultimo_servicio(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha_ultimo_servicio:
                conteo[registro.fecha_ultimo_servicio[:7]] += 1
        return dict(sorted(conteo.items()))

    def buscar_texto(self, termino: str) -> List[Vehiculo]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_tipo": self.conteo_por_tipo(),
        }


def reporte_vehiculos(repo: RepositorioVehiculos, limite: int = 25) -> str:
    """Listado en texto plano de vehículos."""
    encabezados = ['ID', 'Placas', 'Marca', 'Modelo', 'Año', 'Tipo']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.placas,
            truncar(r.marca, 28),
            truncar(r.modelo, 28),
            r.anio,
            r.tipo,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Vehículos ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_vehiculos_demo(n: int = 10, semilla: int = 23) -> List[Vehiculo]:
    """Genera ``n`` registros de vehículos reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Vehiculo] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["placas"] = placas_demo(rng)
        v["marca"] = rng.choice(("Nissan", "Ford", "Chevrolet", "International", "Isuzu", "Hino", "Volkswagen", "Italika"))
        v["modelo"] = rng.choice(("NP300", "Ranger", "Silverado", "4300", "ELF 400", "Serie 300", "Crafter", "FT150"))
        v["anio"] = rng.randint(2008, 2026)
        v["tipo"] = rng.choice(OPCIONES_VEHICULO_TIPO)
        v["capacidad_kg"] = rng.choice((150, 1000, 3500, 8000, 14_000))
        v["kilometraje"] = rng.randint(0, 450_000)
        v["en_servicio"] = rng.random() < 0.9
        v["fecha_ultimo_servicio"] = fecha_aleatoria_demo(rng, date(2025, 1, 1), date(2026, 11, 1)) if rng.random() < 0.8 else ""
        registros.append(Vehiculo(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Ruta  (Rutas)
# ----------------------------------------------------------------------------

_PATRON_RUTA_CLAVE = re.compile(r"^R\d{3}$")


@dataclass
class Ruta:
    """Ruta de reparto programada."""

    id: int
    clave: str
    nombre: str
    origen: str
    destino: str
    distancia_km: float
    tiempo_estimado_min: int
    peaje: float = 0.0
    activa: bool = True

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.clave, str) or not _PATRON_RUTA_CLAVE.match(self.clave):
            errores.append("clave tiene un formato inválido")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 80:
            errores.append("nombre excede 80 caracteres")
        if not isinstance(self.origen, str) or not self.origen.strip():
            errores.append("origen es obligatorio")
        elif len(self.origen) > 60:
            errores.append("origen excede 60 caracteres")
        if not isinstance(self.destino, str) or not self.destino.strip():
            errores.append("destino es obligatorio")
        elif len(self.destino) > 60:
            errores.append("destino excede 60 caracteres")
        if not isinstance(self.distancia_km, (int, float)) or isinstance(self.distancia_km, bool) or not 1 <= self.distancia_km <= 1200:
            errores.append("distancia_km debe estar entre 1 y 1200")
        if not isinstance(self.tiempo_estimado_min, int) or isinstance(self.tiempo_estimado_min, bool) or not 5 <= self.tiempo_estimado_min <= 3000:
            errores.append("tiempo_estimado_min debe ser un entero entre 5 y 3000")
        if not isinstance(self.peaje, (int, float)) or isinstance(self.peaje, bool) or not 0 <= self.peaje <= 5000:
            errores.append("peaje debe estar entre 0 y 5000")
        if not isinstance(self.activa, bool):
            errores.append("activa debe ser booleano")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.tiempo_estimado_min < self.distancia_km * 0.5:
                errores.append("el tiempo estimado implica una velocidad promedio mayor a 120 km/h")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Ruta":
        return cls(
            id=int(datos["id"]),
            clave=str(datos["clave"]),
            nombre=str(datos["nombre"]),
            origen=str(datos["origen"]),
            destino=str(datos["destino"]),
            distancia_km=float(datos["distancia_km"]),
            tiempo_estimado_min=int(datos["tiempo_estimado_min"]),
            peaje=float(datos.get("peaje", 0.0)),
            activa=a_booleano(datos.get("activa", True)),
        )

    def velocidad_promedio_kmh(self) -> float:
        return round(self.distancia_km / (self.tiempo_estimado_min / 60), 1)


class RepositorioRutas(RepositorioMemoria):
    """Repositorio en memoria de rutas."""

    entidad = Ruta
    nombre = "rutas"
    CAMPOS_TEXTO = ('nombre', 'origen', 'destino')

    def con_clave(self, valor: str) -> List[Ruta]:
        return [r for r in self.listar() if r.clave == valor]

    def total_distancia_km(self) -> float:
        return round(sum(r.distancia_km for r in self._items.values()), 2)

    def promedio_distancia_km(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.distancia_km for r in self._items.values()), 2)

    def con_distancia_km_entre(self, minimo: float, maximo: float) -> List[Ruta]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.distancia_km <= maximo]

    def mayores_por_distancia_km(self, n: int = 5) -> List[Ruta]:
        return sorted(self._items.values(), key=lambda r: (-r.distancia_km, r.id))[:n]

    def con_tiempo_estimado_min_entre(self, minimo: int, maximo: int) -> List[Ruta]:
        return [r for r in self.listar() if minimo <= r.tiempo_estimado_min <= maximo]

    def maximo_tiempo_estimado_min(self) -> Optional[int]:
        valores = [r.tiempo_estimado_min for r in self._items.values()]
        return max(valores) if valores else None

    def total_peaje(self) -> float:
        return round(sum(r.peaje for r in self._items.values()), 2)

    def promedio_peaje(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.peaje for r in self._items.values()), 2)

    def con_peaje_entre(self, minimo: float, maximo: float) -> List[Ruta]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.peaje <= maximo]

    def mayores_por_peaje(self, n: int = 5) -> List[Ruta]:
        return sorted(self._items.values(), key=lambda r: (-r.peaje, r.id))[:n]

    def donde_activa(self, valor: bool = True) -> List[Ruta]:
        return [r for r in self.listar() if r.activa is valor]

    def buscar_texto(self, termino: str) -> List[Ruta]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "total_peaje": self.total_peaje(),
        }


def reporte_rutas(repo: RepositorioRutas, limite: int = 25) -> str:
    """Listado en texto plano de rutas."""
    encabezados = ['ID', 'Clave', 'Nombre', 'Origen', 'Destino', 'Km']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.clave,
            truncar(r.nombre, 28),
            truncar(r.origen, 28),
            truncar(r.destino, 28),
            f"{r.distancia_km:.2f}",
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Rutas ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_rutas_demo(n: int = 10, semilla: int = 24) -> List[Ruta]:
    """Genera ``n`` registros de rutas reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Ruta] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["clave"] = f"R{i:03d}"
        v["nombre"] = f"{rng.choice(CIUDADES_DEMO)} - {rng.choice(CIUDADES_DEMO)}"
        v["origen"] = "CEDIS Guadalajara"
        v["destino"] = rng.choice(CIUDADES_DEMO)
        v["distancia_km"] = round(rng.uniform(5, 650), 1)
        v["tiempo_estimado_min"] = int(v["distancia_km"] * rng.uniform(0.8, 2.0)) + 5
        v["peaje"] = round(rng.uniform(0, 900), 2) if v["distancia_km"] > 60 else 0.0
        v["activa"] = rng.random() < 0.9
        registros.append(Ruta(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Turno  (Turnos)
# ----------------------------------------------------------------------------

OPCIONES_TURNO_TIPO = ('matutino', 'vespertino', 'nocturno', 'mixto')
_PATRON_TURNO_HORA_ENTRADA = re.compile(r"^([01]\d|2[0-3]):[0-5]\d$")
_PATRON_TURNO_HORA_SALIDA = re.compile(r"^([01]\d|2[0-3]):[0-5]\d$")


@dataclass
class Turno:
    """Turno laboral asignado a un empleado."""

    id: int
    empleado_id: int
    fecha: str
    tipo: str
    hora_entrada: str
    hora_salida: str
    horas_extra: float = 0.0

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.empleado_id, int) or isinstance(self.empleado_id, bool) or not 1 <= self.empleado_id <= 99_999:
            errores.append("empleado_id debe ser un entero entre 1 y 99_999")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if self.tipo not in OPCIONES_TURNO_TIPO:
            errores.append(f"tipo debe ser uno de: {', '.join(OPCIONES_TURNO_TIPO)}")
        if not isinstance(self.hora_entrada, str) or not _PATRON_TURNO_HORA_ENTRADA.match(self.hora_entrada):
            errores.append("hora_entrada tiene un formato inválido")
        if not isinstance(self.hora_salida, str) or not _PATRON_TURNO_HORA_SALIDA.match(self.hora_salida):
            errores.append("hora_salida tiene un formato inválido")
        if not isinstance(self.horas_extra, (int, float)) or isinstance(self.horas_extra, bool) or not 0 <= self.horas_extra <= 12:
            errores.append("horas_extra debe estar entre 0 y 12")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.tipo != "nocturno" and self.hora_salida <= self.hora_entrada:
                errores.append("la hora de salida debe ser posterior a la de entrada")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Turno":
        return cls(
            id=int(datos["id"]),
            empleado_id=int(datos["empleado_id"]),
            fecha=str(datos["fecha"]),
            tipo=str(datos["tipo"]),
            hora_entrada=str(datos["hora_entrada"]),
            hora_salida=str(datos["hora_salida"]),
            horas_extra=float(datos.get("horas_extra", 0.0)),
        )

    def duracion_horas(self) -> float:
        h1, m1 = map(int, self.hora_entrada.split(":"))
        h2, m2 = map(int, self.hora_salida.split(":"))
        minutos = (h2 * 60 + m2) - (h1 * 60 + m1)
        if minutos <= 0:
            minutos += 24 * 60
        return round(minutos / 60 + self.horas_extra, 2)


class RepositorioTurnos(RepositorioMemoria):
    """Repositorio en memoria de turnos."""

    entidad = Turno
    nombre = "turnos"

    def con_empleado_id_entre(self, minimo: int, maximo: int) -> List[Turno]:
        return [r for r in self.listar() if minimo <= r.empleado_id <= maximo]

    def maximo_empleado_id(self) -> Optional[int]:
        valores = [r.empleado_id for r in self._items.values()]
        return max(valores) if valores else None

    def por_fecha_entre(self, inicio: str, fin: str) -> List[Turno]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_tipo(self, valor: str) -> List[Turno]:
        """Registros cuyo campo tipo es ``valor``."""
        if valor not in OPCIONES_TURNO_TIPO:
            raise ValueError(f"tipo inválido: {valor!r}")
        return [r for r in self.listar() if r.tipo == valor]

    def conteo_por_tipo(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_TURNO_TIPO}
        for registro in self._items.values():
            conteo[registro.tipo] += 1
        return conteo

    def con_hora_entrada(self, valor: str) -> List[Turno]:
        return [r for r in self.listar() if r.hora_entrada == valor]

    def con_hora_salida(self, valor: str) -> List[Turno]:
        return [r for r in self.listar() if r.hora_salida == valor]

    def total_horas_extra(self) -> float:
        return round(sum(r.horas_extra for r in self._items.values()), 2)

    def promedio_horas_extra(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.horas_extra for r in self._items.values()), 2)

    def con_horas_extra_entre(self, minimo: float, maximo: float) -> List[Turno]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.horas_extra <= maximo]

    def mayores_por_horas_extra(self, n: int = 5) -> List[Turno]:
        return sorted(self._items.values(), key=lambda r: (-r.horas_extra, r.id))[:n]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_tipo": self.conteo_por_tipo(),
        }


def reporte_turnos(repo: RepositorioTurnos, limite: int = 25) -> str:
    """Listado en texto plano de turnos."""
    encabezados = ['ID', 'Empleado', 'Fecha', 'Tipo', 'Entrada', 'Salida']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.empleado_id,
            r.fecha,
            r.tipo,
            r.hora_entrada,
            r.hora_salida,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Turnos ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_turnos_demo(n: int = 10, semilla: int = 25) -> List[Turno]:
    """Genera ``n`` registros de turnos reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Turno] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["empleado_id"] = rng.randint(1, 800)
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["tipo"] = rng.choice(OPCIONES_TURNO_TIPO)
        v["hora_entrada"] = hora_entrada_demo(rng, v["tipo"])
        v["hora_salida"] = hora_salida_demo(v["hora_entrada"], v["tipo"])
        v["horas_extra"] = float(rng.choice((0, 0, 0, 1, 2, 3)))
        registros.append(Turno(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: VentaRegistrada  (Ventas registradas)
# ----------------------------------------------------------------------------

_PATRON_VENTA_REGISTRADA_FOLIO = re.compile(r"^V-\d{6}$")
_PATRON_VENTA_REGISTRADA_SUCURSAL_CLAVE = re.compile(r"^SUC\d{3}$")
OPCIONES_VENTA_REGISTRADA_FORMA_PAGO = ('efectivo', 'tarjeta_debito', 'tarjeta_credito', 'transferencia', 'vales')


@dataclass
class VentaRegistrada:
    """Venta ya cerrada, tal como se guarda en el histórico."""

    id: int
    folio: str
    sucursal_clave: str
    fecha: str
    cajero_id: int
    num_articulos: int
    subtotal: float
    iva: float
    total: float
    forma_pago: str
    facturada: bool = False

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.folio, str) or not _PATRON_VENTA_REGISTRADA_FOLIO.match(self.folio):
            errores.append("folio tiene un formato inválido")
        if not isinstance(self.sucursal_clave, str) or not _PATRON_VENTA_REGISTRADA_SUCURSAL_CLAVE.match(self.sucursal_clave):
            errores.append("sucursal_clave tiene un formato inválido")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if not isinstance(self.cajero_id, int) or isinstance(self.cajero_id, bool) or not 1 <= self.cajero_id <= 99_999:
            errores.append("cajero_id debe ser un entero entre 1 y 99_999")
        if not isinstance(self.num_articulos, int) or isinstance(self.num_articulos, bool) or not 1 <= self.num_articulos <= 500:
            errores.append("num_articulos debe ser un entero entre 1 y 500")
        if not isinstance(self.subtotal, (int, float)) or isinstance(self.subtotal, bool) or not 0 <= self.subtotal <= 1_000_000:
            errores.append("subtotal debe estar entre 0 y 1_000_000")
        if not isinstance(self.iva, (int, float)) or isinstance(self.iva, bool) or not 0 <= self.iva <= 160_000:
            errores.append("iva debe estar entre 0 y 160_000")
        if not isinstance(self.total, (int, float)) or isinstance(self.total, bool) or not 0 <= self.total <= 1_160_000:
            errores.append("total debe estar entre 0 y 1_160_000")
        if self.forma_pago not in OPCIONES_VENTA_REGISTRADA_FORMA_PAGO:
            errores.append(f"forma_pago debe ser uno de: {', '.join(OPCIONES_VENTA_REGISTRADA_FORMA_PAGO)}")
        if not isinstance(self.facturada, bool):
            errores.append("facturada debe ser booleano")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if abs(self.total - (self.subtotal + self.iva)) > 0.01:
                errores.append("el total no coincide con subtotal + iva")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "VentaRegistrada":
        return cls(
            id=int(datos["id"]),
            folio=str(datos["folio"]),
            sucursal_clave=str(datos["sucursal_clave"]),
            fecha=str(datos["fecha"]),
            cajero_id=int(datos["cajero_id"]),
            num_articulos=int(datos["num_articulos"]),
            subtotal=float(datos["subtotal"]),
            iva=float(datos["iva"]),
            total=float(datos["total"]),
            forma_pago=str(datos["forma_pago"]),
            facturada=a_booleano(datos.get("facturada", False)),
        )


class RepositorioVentasRegistradas(RepositorioMemoria):
    """Repositorio en memoria de ventas registradas."""

    entidad = VentaRegistrada
    nombre = "ventas_registradas"

    def con_folio(self, valor: str) -> List[VentaRegistrada]:
        return [r for r in self.listar() if r.folio == valor]

    def con_sucursal_clave(self, valor: str) -> List[VentaRegistrada]:
        return [r for r in self.listar() if r.sucursal_clave == valor]

    def por_fecha_entre(self, inicio: str, fin: str) -> List[VentaRegistrada]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_cajero_id_entre(self, minimo: int, maximo: int) -> List[VentaRegistrada]:
        return [r for r in self.listar() if minimo <= r.cajero_id <= maximo]

    def maximo_cajero_id(self) -> Optional[int]:
        valores = [r.cajero_id for r in self._items.values()]
        return max(valores) if valores else None

    def con_num_articulos_entre(self, minimo: int, maximo: int) -> List[VentaRegistrada]:
        return [r for r in self.listar() if minimo <= r.num_articulos <= maximo]

    def maximo_num_articulos(self) -> Optional[int]:
        valores = [r.num_articulos for r in self._items.values()]
        return max(valores) if valores else None

    def total_subtotal(self) -> float:
        return round(sum(r.subtotal for r in self._items.values()), 2)

    def promedio_subtotal(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.subtotal for r in self._items.values()), 2)

    def con_subtotal_entre(self, minimo: float, maximo: float) -> List[VentaRegistrada]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.subtotal <= maximo]

    def mayores_por_subtotal(self, n: int = 5) -> List[VentaRegistrada]:
        return sorted(self._items.values(), key=lambda r: (-r.subtotal, r.id))[:n]

    def total_iva(self) -> float:
        return round(sum(r.iva for r in self._items.values()), 2)

    def promedio_iva(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.iva for r in self._items.values()), 2)

    def con_iva_entre(self, minimo: float, maximo: float) -> List[VentaRegistrada]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.iva <= maximo]

    def mayores_por_iva(self, n: int = 5) -> List[VentaRegistrada]:
        return sorted(self._items.values(), key=lambda r: (-r.iva, r.id))[:n]

    def total_total(self) -> float:
        return round(sum(r.total for r in self._items.values()), 2)

    def promedio_total(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.total for r in self._items.values()), 2)

    def con_total_entre(self, minimo: float, maximo: float) -> List[VentaRegistrada]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.total <= maximo]

    def mayores_por_total(self, n: int = 5) -> List[VentaRegistrada]:
        return sorted(self._items.values(), key=lambda r: (-r.total, r.id))[:n]

    def por_forma_pago(self, valor: str) -> List[VentaRegistrada]:
        """Registros cuyo campo forma_pago es ``valor``."""
        if valor not in OPCIONES_VENTA_REGISTRADA_FORMA_PAGO:
            raise ValueError(f"forma_pago inválido: {valor!r}")
        return [r for r in self.listar() if r.forma_pago == valor]

    def conteo_por_forma_pago(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_VENTA_REGISTRADA_FORMA_PAGO}
        for registro in self._items.values():
            conteo[registro.forma_pago] += 1
        return conteo

    def donde_facturada(self, valor: bool = True) -> List[VentaRegistrada]:
        return [r for r in self.listar() if r.facturada is valor]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "total_subtotal": self.total_subtotal(),
            "total_iva": self.total_iva(),
            "total_total": self.total_total(),
            "por_forma_pago": self.conteo_por_forma_pago(),
        }

    def ticket_promedio(self) -> float:
        return self.promedio_total()

    def ventas_por_forma_pago(self) -> Dict[str, float]:
        totales = {forma: 0.0 for forma in OPCIONES_VENTA_REGISTRADA_FORMA_PAGO}
        for venta in self._items.values():
            totales[venta.forma_pago] = round(totales[venta.forma_pago] + venta.total, 2)
        return totales


def reporte_ventas_registradas(repo: RepositorioVentasRegistradas, limite: int = 25) -> str:
    """Listado en texto plano de ventas registradas."""
    encabezados = ['ID', 'Folio', 'Sucursal', 'Fecha', 'Cajero id', 'Num articulos']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.folio,
            r.sucursal_clave,
            r.fecha,
            r.cajero_id,
            r.num_articulos,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Ventas registradas ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_ventas_registradas_demo(n: int = 10, semilla: int = 26) -> List[VentaRegistrada]:
    """Genera ``n`` registros de ventas registradas reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[VentaRegistrada] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["folio"] = f"V-{i:06d}"
        v["sucursal_clave"] = f"SUC{rng.randint(1, 30):03d}"
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["cajero_id"] = rng.randint(1, 800)
        v["num_articulos"] = rng.randint(1, 40)
        v["subtotal"] = round(rng.uniform(15, 4500), 2)
        v["iva"] = round(v["subtotal"] * TASA_IVA, 2)
        v["total"] = round(v["subtotal"] + v["iva"], 2)
        v["forma_pago"] = rng.choice(OPCIONES_VENTA_REGISTRADA_FORMA_PAGO)
        v["facturada"] = rng.random() < 0.2
        registros.append(VentaRegistrada(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: CorteCaja  (Cortes de caja)
# ----------------------------------------------------------------------------

_PATRON_CORTE_CAJA_SUCURSAL_CLAVE = re.compile(r"^SUC\d{3}$")


@dataclass
class CorteCaja:
    """Corte de caja al cierre de turno."""

    id: int
    sucursal_clave: str
    fecha: str
    cajero_id: int
    fondo_inicial: float
    ventas_efectivo: float
    ventas_tarjeta: float
    retiros: float
    efectivo_contado: float
    observaciones: str = ''

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.sucursal_clave, str) or not _PATRON_CORTE_CAJA_SUCURSAL_CLAVE.match(self.sucursal_clave):
            errores.append("sucursal_clave tiene un formato inválido")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if not isinstance(self.cajero_id, int) or isinstance(self.cajero_id, bool) or not 1 <= self.cajero_id <= 99_999:
            errores.append("cajero_id debe ser un entero entre 1 y 99_999")
        if not isinstance(self.fondo_inicial, (int, float)) or isinstance(self.fondo_inicial, bool) or not 0 <= self.fondo_inicial <= 20_000:
            errores.append("fondo_inicial debe estar entre 0 y 20_000")
        if not isinstance(self.ventas_efectivo, (int, float)) or isinstance(self.ventas_efectivo, bool) or not 0 <= self.ventas_efectivo <= 2_000_000:
            errores.append("ventas_efectivo debe estar entre 0 y 2_000_000")
        if not isinstance(self.ventas_tarjeta, (int, float)) or isinstance(self.ventas_tarjeta, bool) or not 0 <= self.ventas_tarjeta <= 2_000_000:
            errores.append("ventas_tarjeta debe estar entre 0 y 2_000_000")
        if not isinstance(self.retiros, (int, float)) or isinstance(self.retiros, bool) or not 0 <= self.retiros <= 2_000_000:
            errores.append("retiros debe estar entre 0 y 2_000_000")
        if not isinstance(self.efectivo_contado, (int, float)) or isinstance(self.efectivo_contado, bool) or not 0 <= self.efectivo_contado <= 2_100_000:
            errores.append("efectivo_contado debe estar entre 0 y 2_100_000")
        if not isinstance(self.observaciones, str):
            errores.append("observaciones debe ser texto")
        elif len(self.observaciones) > 250:
            errores.append("observaciones excede 250 caracteres")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "CorteCaja":
        return cls(
            id=int(datos["id"]),
            sucursal_clave=str(datos["sucursal_clave"]),
            fecha=str(datos["fecha"]),
            cajero_id=int(datos["cajero_id"]),
            fondo_inicial=float(datos["fondo_inicial"]),
            ventas_efectivo=float(datos["ventas_efectivo"]),
            ventas_tarjeta=float(datos["ventas_tarjeta"]),
            retiros=float(datos["retiros"]),
            efectivo_contado=float(datos["efectivo_contado"]),
            observaciones=str(datos.get("observaciones", '')),
        )

    def efectivo_esperado(self) -> float:
        return round(self.fondo_inicial + self.ventas_efectivo - self.retiros, 2)

    def diferencia(self) -> float:
        """Positivo = sobrante, negativo = faltante."""
        return round(self.efectivo_contado - self.efectivo_esperado(), 2)


class RepositorioCortesCaja(RepositorioMemoria):
    """Repositorio en memoria de cortes de caja."""

    entidad = CorteCaja
    nombre = "cortes_caja"
    CAMPOS_TEXTO = ('observaciones',)

    def con_sucursal_clave(self, valor: str) -> List[CorteCaja]:
        return [r for r in self.listar() if r.sucursal_clave == valor]

    def por_fecha_entre(self, inicio: str, fin: str) -> List[CorteCaja]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_cajero_id_entre(self, minimo: int, maximo: int) -> List[CorteCaja]:
        return [r for r in self.listar() if minimo <= r.cajero_id <= maximo]

    def maximo_cajero_id(self) -> Optional[int]:
        valores = [r.cajero_id for r in self._items.values()]
        return max(valores) if valores else None

    def total_fondo_inicial(self) -> float:
        return round(sum(r.fondo_inicial for r in self._items.values()), 2)

    def promedio_fondo_inicial(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.fondo_inicial for r in self._items.values()), 2)

    def con_fondo_inicial_entre(self, minimo: float, maximo: float) -> List[CorteCaja]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.fondo_inicial <= maximo]

    def mayores_por_fondo_inicial(self, n: int = 5) -> List[CorteCaja]:
        return sorted(self._items.values(), key=lambda r: (-r.fondo_inicial, r.id))[:n]

    def total_ventas_efectivo(self) -> float:
        return round(sum(r.ventas_efectivo for r in self._items.values()), 2)

    def promedio_ventas_efectivo(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.ventas_efectivo for r in self._items.values()), 2)

    def con_ventas_efectivo_entre(self, minimo: float, maximo: float) -> List[CorteCaja]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.ventas_efectivo <= maximo]

    def mayores_por_ventas_efectivo(self, n: int = 5) -> List[CorteCaja]:
        return sorted(self._items.values(), key=lambda r: (-r.ventas_efectivo, r.id))[:n]

    def total_ventas_tarjeta(self) -> float:
        return round(sum(r.ventas_tarjeta for r in self._items.values()), 2)

    def promedio_ventas_tarjeta(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.ventas_tarjeta for r in self._items.values()), 2)

    def con_ventas_tarjeta_entre(self, minimo: float, maximo: float) -> List[CorteCaja]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.ventas_tarjeta <= maximo]

    def mayores_por_ventas_tarjeta(self, n: int = 5) -> List[CorteCaja]:
        return sorted(self._items.values(), key=lambda r: (-r.ventas_tarjeta, r.id))[:n]

    def total_retiros(self) -> float:
        return round(sum(r.retiros for r in self._items.values()), 2)

    def promedio_retiros(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.retiros for r in self._items.values()), 2)

    def con_retiros_entre(self, minimo: float, maximo: float) -> List[CorteCaja]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.retiros <= maximo]

    def mayores_por_retiros(self, n: int = 5) -> List[CorteCaja]:
        return sorted(self._items.values(), key=lambda r: (-r.retiros, r.id))[:n]

    def total_efectivo_contado(self) -> float:
        return round(sum(r.efectivo_contado for r in self._items.values()), 2)

    def promedio_efectivo_contado(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.efectivo_contado for r in self._items.values()), 2)

    def con_efectivo_contado_entre(self, minimo: float, maximo: float) -> List[CorteCaja]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.efectivo_contado <= maximo]

    def mayores_por_efectivo_contado(self, n: int = 5) -> List[CorteCaja]:
        return sorted(self._items.values(), key=lambda r: (-r.efectivo_contado, r.id))[:n]

    def buscar_texto(self, termino: str) -> List[CorteCaja]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "total_fondo_inicial": self.total_fondo_inicial(),
            "total_ventas_efectivo": self.total_ventas_efectivo(),
            "total_ventas_tarjeta": self.total_ventas_tarjeta(),
            "total_retiros": self.total_retiros(),
            "total_efectivo_contado": self.total_efectivo_contado(),
        }

    def con_faltante(self, tolerancia: float = 1.0) -> List[CorteCaja]:
        return [c for c in self.listar() if c.diferencia() < -tolerancia]


def reporte_cortes_caja(repo: RepositorioCortesCaja, limite: int = 25) -> str:
    """Listado en texto plano de cortes de caja."""
    encabezados = ['ID', 'Sucursal', 'Fecha', 'Cajero', 'Fondo inicial', 'Efectivo']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.sucursal_clave,
            r.fecha,
            r.cajero_id,
            formatear_moneda(r.fondo_inicial),
            formatear_moneda(r.ventas_efectivo),
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Cortes de caja ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_cortes_caja_demo(n: int = 10, semilla: int = 27) -> List[CorteCaja]:
    """Genera ``n`` registros de cortes de caja reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[CorteCaja] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["sucursal_clave"] = f"SUC{rng.randint(1, 30):03d}"
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["cajero_id"] = rng.randint(1, 800)
        v["fondo_inicial"] = float(rng.choice((1000, 1500, 2000, 3000)))
        v["ventas_efectivo"] = round(rng.uniform(2000, 60_000), 2)
        v["ventas_tarjeta"] = round(rng.uniform(1000, 80_000), 2)
        v["retiros"] = round(rng.uniform(0, v["ventas_efectivo"] * 0.6), 2)
        v["efectivo_contado"] = round(v["fondo_inicial"] + v["ventas_efectivo"] - v["retiros"] + rng.choice((0, 0, 0, -50, 20, -5.5)), 2)
        v["observaciones"] = frase_demo(rng, 4) if rng.random() < 0.3 else ""
        registros.append(CorteCaja(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Auditoria  (Bitácora de auditoría)
# ----------------------------------------------------------------------------

OPCIONES_AUDITORIA_ACCION = ('alta', 'baja', 'cambio', 'consulta', 'login', 'logout')
_PATRON_AUDITORIA_IP = re.compile(r"^(\d{1,3}\.){3}\d{1,3}$")


@dataclass
class Auditoria:
    """Evento registrado en la bitácora de auditoría."""

    id: int
    fecha: str
    usuario: str
    accion: str
    entidad: str
    entidad_id: int
    ip: str
    detalle: str = ''
    exitosa: bool = True

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if not isinstance(self.usuario, str) or not self.usuario.strip():
            errores.append("usuario es obligatorio")
        elif len(self.usuario) > 40:
            errores.append("usuario excede 40 caracteres")
        if self.accion not in OPCIONES_AUDITORIA_ACCION:
            errores.append(f"accion debe ser uno de: {', '.join(OPCIONES_AUDITORIA_ACCION)}")
        if not isinstance(self.entidad, str) or not self.entidad.strip():
            errores.append("entidad es obligatorio")
        elif len(self.entidad) > 40:
            errores.append("entidad excede 40 caracteres")
        if not isinstance(self.entidad_id, int) or isinstance(self.entidad_id, bool) or not 0 <= self.entidad_id <= 1_000_000_000:
            errores.append("entidad_id debe ser un entero entre 0 y 1_000_000_000")
        if not isinstance(self.ip, str) or not _PATRON_AUDITORIA_IP.match(self.ip):
            errores.append("ip tiene un formato inválido")
        if not isinstance(self.detalle, str):
            errores.append("detalle debe ser texto")
        elif len(self.detalle) > 300:
            errores.append("detalle excede 300 caracteres")
        if not isinstance(self.exitosa, bool):
            errores.append("exitosa debe ser booleano")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Auditoria":
        return cls(
            id=int(datos["id"]),
            fecha=str(datos["fecha"]),
            usuario=str(datos["usuario"]),
            accion=str(datos["accion"]),
            entidad=str(datos["entidad"]),
            entidad_id=int(datos["entidad_id"]),
            ip=str(datos["ip"]),
            detalle=str(datos.get("detalle", '')),
            exitosa=a_booleano(datos.get("exitosa", True)),
        )


class RepositorioAuditorias(RepositorioMemoria):
    """Repositorio en memoria de bitácora de auditoría."""

    entidad = Auditoria
    nombre = "auditorias"
    CAMPOS_TEXTO = ('usuario', 'entidad', 'detalle')

    def por_fecha_entre(self, inicio: str, fin: str) -> List[Auditoria]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_accion(self, valor: str) -> List[Auditoria]:
        """Registros cuyo campo accion es ``valor``."""
        if valor not in OPCIONES_AUDITORIA_ACCION:
            raise ValueError(f"accion inválido: {valor!r}")
        return [r for r in self.listar() if r.accion == valor]

    def conteo_por_accion(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_AUDITORIA_ACCION}
        for registro in self._items.values():
            conteo[registro.accion] += 1
        return conteo

    def con_entidad_id_entre(self, minimo: int, maximo: int) -> List[Auditoria]:
        return [r for r in self.listar() if minimo <= r.entidad_id <= maximo]

    def maximo_entidad_id(self) -> Optional[int]:
        valores = [r.entidad_id for r in self._items.values()]
        return max(valores) if valores else None

    def con_ip(self, valor: str) -> List[Auditoria]:
        return [r for r in self.listar() if r.ip == valor]

    def donde_exitosa(self, valor: bool = True) -> List[Auditoria]:
        return [r for r in self.listar() if r.exitosa is valor]

    def buscar_texto(self, termino: str) -> List[Auditoria]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_accion": self.conteo_por_accion(),
        }

    def fallidas(self) -> List[Auditoria]:
        return [a for a in self.listar() if not a.exitosa]

    def actividad_por_usuario(self) -> Dict[str, int]:
        return dict(Counter(a.usuario for a in self._items.values()).most_common())


def reporte_auditorias(repo: RepositorioAuditorias, limite: int = 25) -> str:
    """Listado en texto plano de bitácora de auditoría."""
    encabezados = ['ID', 'Fecha', 'Usuario', 'Acción', 'Entidad', 'Entidad id']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.fecha,
            truncar(r.usuario, 28),
            r.accion,
            truncar(r.entidad, 28),
            r.entidad_id,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Bitácora de auditoría ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_auditorias_demo(n: int = 10, semilla: int = 28) -> List[Auditoria]:
    """Genera ``n`` registros de bitácora de auditoría reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Auditoria] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["usuario"] = slugify(rng.choice(NOMBRES_DEMO)).replace("-", "_") + str(rng.randint(1, 99))
        v["accion"] = rng.choice(OPCIONES_AUDITORIA_ACCION)
        v["entidad"] = rng.choice(("Producto", "Cliente", "Proveedor", "Venta", "Factura", "Usuario"))
        v["entidad_id"] = rng.randint(1, 50_000)
        v["ip"] = ip_demo(rng)
        v["detalle"] = frase_demo(rng, 6) if rng.random() < 0.5 else ""
        v["exitosa"] = rng.random() < 0.95
        registros.append(Auditoria(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Mantenimiento  (Mantenimientos)
# ----------------------------------------------------------------------------

_PATRON_MANTENIMIENTO_VEHICULO_PLACAS = re.compile(r"^[A-Z]{3}-\d{3}-[A-Z]$")
OPCIONES_MANTENIMIENTO_TIPO = ('preventivo', 'correctivo', 'llantas', 'verificacion')


@dataclass
class Mantenimiento:
    """Servicio de mantenimiento a un vehículo."""

    id: int
    vehiculo_placas: str
    fecha: str
    tipo: str
    costo: float
    kilometraje: int
    taller: str
    garantia_dias: int = 0

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.vehiculo_placas, str) or not _PATRON_MANTENIMIENTO_VEHICULO_PLACAS.match(self.vehiculo_placas):
            errores.append("vehiculo_placas tiene un formato inválido")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if self.tipo not in OPCIONES_MANTENIMIENTO_TIPO:
            errores.append(f"tipo debe ser uno de: {', '.join(OPCIONES_MANTENIMIENTO_TIPO)}")
        if not isinstance(self.costo, (int, float)) or isinstance(self.costo, bool) or not 0 <= self.costo <= 500_000:
            errores.append("costo debe estar entre 0 y 500_000")
        if not isinstance(self.kilometraje, int) or isinstance(self.kilometraje, bool) or not 0 <= self.kilometraje <= 900_000:
            errores.append("kilometraje debe ser un entero entre 0 y 900_000")
        if not isinstance(self.taller, str) or not self.taller.strip():
            errores.append("taller es obligatorio")
        elif len(self.taller) > 100:
            errores.append("taller excede 100 caracteres")
        if not isinstance(self.garantia_dias, int) or isinstance(self.garantia_dias, bool) or not 0 <= self.garantia_dias <= 365:
            errores.append("garantia_dias debe ser un entero entre 0 y 365")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Mantenimiento":
        return cls(
            id=int(datos["id"]),
            vehiculo_placas=str(datos["vehiculo_placas"]),
            fecha=str(datos["fecha"]),
            tipo=str(datos["tipo"]),
            costo=float(datos["costo"]),
            kilometraje=int(datos["kilometraje"]),
            taller=str(datos["taller"]),
            garantia_dias=int(datos.get("garantia_dias", 0)),
        )


class RepositorioMantenimientos(RepositorioMemoria):
    """Repositorio en memoria de mantenimientos."""

    entidad = Mantenimiento
    nombre = "mantenimientos"
    CAMPOS_TEXTO = ('taller',)

    def con_vehiculo_placas(self, valor: str) -> List[Mantenimiento]:
        return [r for r in self.listar() if r.vehiculo_placas == valor]

    def por_fecha_entre(self, inicio: str, fin: str) -> List[Mantenimiento]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_tipo(self, valor: str) -> List[Mantenimiento]:
        """Registros cuyo campo tipo es ``valor``."""
        if valor not in OPCIONES_MANTENIMIENTO_TIPO:
            raise ValueError(f"tipo inválido: {valor!r}")
        return [r for r in self.listar() if r.tipo == valor]

    def conteo_por_tipo(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_MANTENIMIENTO_TIPO}
        for registro in self._items.values():
            conteo[registro.tipo] += 1
        return conteo

    def total_costo(self) -> float:
        return round(sum(r.costo for r in self._items.values()), 2)

    def promedio_costo(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.costo for r in self._items.values()), 2)

    def con_costo_entre(self, minimo: float, maximo: float) -> List[Mantenimiento]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.costo <= maximo]

    def mayores_por_costo(self, n: int = 5) -> List[Mantenimiento]:
        return sorted(self._items.values(), key=lambda r: (-r.costo, r.id))[:n]

    def con_kilometraje_entre(self, minimo: int, maximo: int) -> List[Mantenimiento]:
        return [r for r in self.listar() if minimo <= r.kilometraje <= maximo]

    def maximo_kilometraje(self) -> Optional[int]:
        valores = [r.kilometraje for r in self._items.values()]
        return max(valores) if valores else None

    def con_garantia_dias_entre(self, minimo: int, maximo: int) -> List[Mantenimiento]:
        return [r for r in self.listar() if minimo <= r.garantia_dias <= maximo]

    def maximo_garantia_dias(self) -> Optional[int]:
        valores = [r.garantia_dias for r in self._items.values()]
        return max(valores) if valores else None

    def buscar_texto(self, termino: str) -> List[Mantenimiento]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_tipo": self.conteo_por_tipo(),
            "total_costo": self.total_costo(),
        }


def reporte_mantenimientos(repo: RepositorioMantenimientos, limite: int = 25) -> str:
    """Listado en texto plano de mantenimientos."""
    encabezados = ['ID', 'Placas', 'Fecha', 'Tipo', 'Costo', 'Kilometraje']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.vehiculo_placas,
            r.fecha,
            r.tipo,
            formatear_moneda(r.costo),
            r.kilometraje,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Mantenimientos ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_mantenimientos_demo(n: int = 10, semilla: int = 29) -> List[Mantenimiento]:
    """Genera ``n`` registros de mantenimientos reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Mantenimiento] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["vehiculo_placas"] = placas_demo(rng)
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["tipo"] = rng.choice(OPCIONES_MANTENIMIENTO_TIPO)
        v["costo"] = round(rng.uniform(450, 38_000), 2)
        v["kilometraje"] = rng.randint(1000, 450_000)
        v["taller"] = rng.choice(TALLERES_DEMO)
        v["garantia_dias"] = rng.choice((0, 30, 90, 180))
        registros.append(Mantenimiento(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Gasto  (Gastos)
# ----------------------------------------------------------------------------

OPCIONES_GASTO_CATEGORIA = ('renta', 'luz', 'agua', 'nomina', 'mantenimiento', 'publicidad', 'papeleria', 'otros')
_PATRON_GASTO_SUCURSAL_CLAVE = re.compile(r"^SUC\d{3}$")


@dataclass
class Gasto:
    """Gasto operativo de una sucursal."""

    id: int
    concepto: str
    categoria: str
    monto: float
    fecha: str
    sucursal_clave: str
    deducible: bool = True
    rfc_proveedor: str = ''

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.concepto, str) or not self.concepto.strip():
            errores.append("concepto es obligatorio")
        elif len(self.concepto) > 120:
            errores.append("concepto excede 120 caracteres")
        if self.categoria not in OPCIONES_GASTO_CATEGORIA:
            errores.append(f"categoria debe ser uno de: {', '.join(OPCIONES_GASTO_CATEGORIA)}")
        if not isinstance(self.monto, (int, float)) or isinstance(self.monto, bool) or not 0.01 <= self.monto <= 1_000_000:
            errores.append("monto debe estar entre 0.01 y 1_000_000")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if not isinstance(self.sucursal_clave, str) or not _PATRON_GASTO_SUCURSAL_CLAVE.match(self.sucursal_clave):
            errores.append("sucursal_clave tiene un formato inválido")
        if not isinstance(self.deducible, bool):
            errores.append("deducible debe ser booleano")
        if self.rfc_proveedor and not es_rfc_valido(self.rfc_proveedor):
            errores.append("rfc_proveedor no es un RFC válido")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Gasto":
        return cls(
            id=int(datos["id"]),
            concepto=str(datos["concepto"]),
            categoria=str(datos["categoria"]),
            monto=float(datos["monto"]),
            fecha=str(datos["fecha"]),
            sucursal_clave=str(datos["sucursal_clave"]),
            deducible=a_booleano(datos.get("deducible", True)),
            rfc_proveedor=str(datos.get("rfc_proveedor", '')),
        )


class RepositorioGastos(RepositorioMemoria):
    """Repositorio en memoria de gastos."""

    entidad = Gasto
    nombre = "gastos"
    CAMPOS_TEXTO = ('concepto',)

    def por_categoria(self, valor: str) -> List[Gasto]:
        """Registros cuyo campo categoria es ``valor``."""
        if valor not in OPCIONES_GASTO_CATEGORIA:
            raise ValueError(f"categoria inválido: {valor!r}")
        return [r for r in self.listar() if r.categoria == valor]

    def conteo_por_categoria(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_GASTO_CATEGORIA}
        for registro in self._items.values():
            conteo[registro.categoria] += 1
        return conteo

    def total_monto(self) -> float:
        return round(sum(r.monto for r in self._items.values()), 2)

    def promedio_monto(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.monto for r in self._items.values()), 2)

    def con_monto_entre(self, minimo: float, maximo: float) -> List[Gasto]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.monto <= maximo]

    def mayores_por_monto(self, n: int = 5) -> List[Gasto]:
        return sorted(self._items.values(), key=lambda r: (-r.monto, r.id))[:n]

    def por_fecha_entre(self, inicio: str, fin: str) -> List[Gasto]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_sucursal_clave(self, valor: str) -> List[Gasto]:
        return [r for r in self.listar() if r.sucursal_clave == valor]

    def donde_deducible(self, valor: bool = True) -> List[Gasto]:
        return [r for r in self.listar() if r.deducible is valor]

    def buscar_texto(self, termino: str) -> List[Gasto]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_categoria": self.conteo_por_categoria(),
            "total_monto": self.total_monto(),
        }

    def total_deducible(self) -> float:
        return round(sum(g.monto for g in self._items.values() if g.deducible), 2)


def reporte_gastos(repo: RepositorioGastos, limite: int = 25) -> str:
    """Listado en texto plano de gastos."""
    encabezados = ['ID', 'Concepto', 'Categoría', 'Monto', 'Fecha', 'Sucursal']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            truncar(r.concepto, 28),
            r.categoria,
            formatear_moneda(r.monto),
            r.fecha,
            r.sucursal_clave,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Gastos ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_gastos_demo(n: int = 10, semilla: int = 30) -> List[Gasto]:
    """Genera ``n`` registros de gastos reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Gasto] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["concepto"] = rng.choice(CONCEPTOS_GASTO_DEMO)
        v["categoria"] = rng.choice(OPCIONES_GASTO_CATEGORIA)
        v["monto"] = round(rng.uniform(150, 85_000), 2)
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["sucursal_clave"] = f"SUC{rng.randint(1, 30):03d}"
        v["deducible"] = rng.random() < 0.8
        v["rfc_proveedor"] = generar_rfc_demo(rng, moral=True) if rng.random() < 0.7 else ""
        registros.append(Gasto(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Queja  (Quejas)
# ----------------------------------------------------------------------------

OPCIONES_QUEJA_CANAL = ('tienda', 'telefono', 'correo', 'redes', 'app')
OPCIONES_QUEJA_PRIORIDAD = ('baja', 'media', 'alta', 'critica')


@dataclass
class Queja:
    """Queja o sugerencia de un cliente."""

    id: int
    cliente_id: int
    fecha: str
    canal: str
    prioridad: str
    descripcion: str
    resuelta: bool = False
    dias_resolucion: int = 0

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.cliente_id, int) or isinstance(self.cliente_id, bool) or not 1 <= self.cliente_id <= 10_000_000:
            errores.append("cliente_id debe ser un entero entre 1 y 10_000_000")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if self.canal not in OPCIONES_QUEJA_CANAL:
            errores.append(f"canal debe ser uno de: {', '.join(OPCIONES_QUEJA_CANAL)}")
        if self.prioridad not in OPCIONES_QUEJA_PRIORIDAD:
            errores.append(f"prioridad debe ser uno de: {', '.join(OPCIONES_QUEJA_PRIORIDAD)}")
        if not isinstance(self.descripcion, str) or not self.descripcion.strip():
            errores.append("descripcion es obligatorio")
        elif len(self.descripcion) > 500:
            errores.append("descripcion excede 500 caracteres")
        if not isinstance(self.resuelta, bool):
            errores.append("resuelta debe ser booleano")
        if not isinstance(self.dias_resolucion, int) or isinstance(self.dias_resolucion, bool) or not 0 <= self.dias_resolucion <= 365:
            errores.append("dias_resolucion debe ser un entero entre 0 y 365")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if not self.resuelta and self.dias_resolucion > 0:
                errores.append("una queja abierta no puede tener días de resolución")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Queja":
        return cls(
            id=int(datos["id"]),
            cliente_id=int(datos["cliente_id"]),
            fecha=str(datos["fecha"]),
            canal=str(datos["canal"]),
            prioridad=str(datos["prioridad"]),
            descripcion=str(datos["descripcion"]),
            resuelta=a_booleano(datos.get("resuelta", False)),
            dias_resolucion=int(datos.get("dias_resolucion", 0)),
        )


class RepositorioQuejas(RepositorioMemoria):
    """Repositorio en memoria de quejas."""

    entidad = Queja
    nombre = "quejas"
    CAMPOS_TEXTO = ('descripcion',)

    def con_cliente_id_entre(self, minimo: int, maximo: int) -> List[Queja]:
        return [r for r in self.listar() if minimo <= r.cliente_id <= maximo]

    def maximo_cliente_id(self) -> Optional[int]:
        valores = [r.cliente_id for r in self._items.values()]
        return max(valores) if valores else None

    def por_fecha_entre(self, inicio: str, fin: str) -> List[Queja]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_canal(self, valor: str) -> List[Queja]:
        """Registros cuyo campo canal es ``valor``."""
        if valor not in OPCIONES_QUEJA_CANAL:
            raise ValueError(f"canal inválido: {valor!r}")
        return [r for r in self.listar() if r.canal == valor]

    def conteo_por_canal(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_QUEJA_CANAL}
        for registro in self._items.values():
            conteo[registro.canal] += 1
        return conteo

    def por_prioridad(self, valor: str) -> List[Queja]:
        """Registros cuyo campo prioridad es ``valor``."""
        if valor not in OPCIONES_QUEJA_PRIORIDAD:
            raise ValueError(f"prioridad inválido: {valor!r}")
        return [r for r in self.listar() if r.prioridad == valor]

    def conteo_por_prioridad(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_QUEJA_PRIORIDAD}
        for registro in self._items.values():
            conteo[registro.prioridad] += 1
        return conteo

    def donde_resuelta(self, valor: bool = True) -> List[Queja]:
        return [r for r in self.listar() if r.resuelta is valor]

    def con_dias_resolucion_entre(self, minimo: int, maximo: int) -> List[Queja]:
        return [r for r in self.listar() if minimo <= r.dias_resolucion <= maximo]

    def maximo_dias_resolucion(self) -> Optional[int]:
        valores = [r.dias_resolucion for r in self._items.values()]
        return max(valores) if valores else None

    def buscar_texto(self, termino: str) -> List[Queja]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_canal": self.conteo_por_canal(),
            "por_prioridad": self.conteo_por_prioridad(),
        }

    def abiertas_por_prioridad(self) -> Dict[str, int]:
        conteo = {p: 0 for p in OPCIONES_QUEJA_PRIORIDAD}
        for queja in self._items.values():
            if not queja.resuelta:
                conteo[queja.prioridad] += 1
        return conteo


def reporte_quejas(repo: RepositorioQuejas, limite: int = 25) -> str:
    """Listado en texto plano de quejas."""
    encabezados = ['ID', 'Cliente', 'Fecha', 'Canal', 'Prioridad', 'Descripción']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.cliente_id,
            r.fecha,
            r.canal,
            r.prioridad,
            truncar(r.descripcion, 28),
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Quejas ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_quejas_demo(n: int = 10, semilla: int = 31) -> List[Queja]:
    """Genera ``n`` registros de quejas reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Queja] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["cliente_id"] = rng.randint(1, 20_000)
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["canal"] = rng.choice(OPCIONES_QUEJA_CANAL)
        v["prioridad"] = rng.choice(OPCIONES_QUEJA_PRIORIDAD)
        v["descripcion"] = frase_demo(rng, 8)
        v["resuelta"] = rng.random() < 0.6
        v["dias_resolucion"] = rng.randint(0, 30) if v["resuelta"] else 0
        registros.append(Queja(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: ListaPrecio  (Listas de precios)
# ----------------------------------------------------------------------------

_PATRON_LISTA_PRECIO_CLAVE = re.compile(r"^LP\d{2}$")
OPCIONES_LISTA_PRECIO_TIPO_CLIENTE = ('mostrador', 'mayoreo', 'institucional', 'en_linea')
OPCIONES_LISTA_PRECIO_MONEDA = ('MXN', 'USD')


@dataclass
class ListaPrecio:
    """Lista de precios por tipo de cliente."""

    id: int
    clave: str
    nombre: str
    tipo_cliente: str
    descuento_general: float
    vigente_desde: str
    vigente_hasta: str = ''
    moneda: str = 'MXN'

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.clave, str) or not _PATRON_LISTA_PRECIO_CLAVE.match(self.clave):
            errores.append("clave tiene un formato inválido")
        if not isinstance(self.nombre, str) or not self.nombre.strip():
            errores.append("nombre es obligatorio")
        elif len(self.nombre) > 80:
            errores.append("nombre excede 80 caracteres")
        if self.tipo_cliente not in OPCIONES_LISTA_PRECIO_TIPO_CLIENTE:
            errores.append(f"tipo_cliente debe ser uno de: {', '.join(OPCIONES_LISTA_PRECIO_TIPO_CLIENTE)}")
        if not isinstance(self.descuento_general, (int, float)) or isinstance(self.descuento_general, bool) or not 0 <= self.descuento_general <= 50:
            errores.append("descuento_general debe estar entre 0 y 50")
        if not es_fecha_iso(self.vigente_desde):
            errores.append("vigente_desde debe tener formato AAAA-MM-DD")
        if self.vigente_hasta and not es_fecha_iso(self.vigente_hasta):
            errores.append("vigente_hasta debe tener formato AAAA-MM-DD")
        if self.moneda not in OPCIONES_LISTA_PRECIO_MONEDA:
            errores.append(f"moneda debe ser uno de: {', '.join(OPCIONES_LISTA_PRECIO_MONEDA)}")
        # Reglas de negocio que involucran más de un campo
        if not errores:
            if self.vigente_hasta and self.vigente_hasta < self.vigente_desde:
                errores.append("vigente_hasta no puede ser anterior a vigente_desde")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "ListaPrecio":
        return cls(
            id=int(datos["id"]),
            clave=str(datos["clave"]),
            nombre=str(datos["nombre"]),
            tipo_cliente=str(datos["tipo_cliente"]),
            descuento_general=float(datos["descuento_general"]),
            vigente_desde=str(datos["vigente_desde"]),
            vigente_hasta=str(datos.get("vigente_hasta", '')),
            moneda=str(datos.get("moneda", 'MXN')),
        )

    def precio_para(self, precio_lista: float) -> float:
        return aplicar_descuento(precio_lista, self.descuento_general)


class RepositorioListasPrecios(RepositorioMemoria):
    """Repositorio en memoria de listas de precios."""

    entidad = ListaPrecio
    nombre = "listas_precios"
    CAMPOS_TEXTO = ('nombre',)

    def con_clave(self, valor: str) -> List[ListaPrecio]:
        return [r for r in self.listar() if r.clave == valor]

    def por_tipo_cliente(self, valor: str) -> List[ListaPrecio]:
        """Registros cuyo campo tipo_cliente es ``valor``."""
        if valor not in OPCIONES_LISTA_PRECIO_TIPO_CLIENTE:
            raise ValueError(f"tipo_cliente inválido: {valor!r}")
        return [r for r in self.listar() if r.tipo_cliente == valor]

    def conteo_por_tipo_cliente(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_LISTA_PRECIO_TIPO_CLIENTE}
        for registro in self._items.values():
            conteo[registro.tipo_cliente] += 1
        return conteo

    def total_descuento_general(self) -> float:
        return round(sum(r.descuento_general for r in self._items.values()), 2)

    def promedio_descuento_general(self) -> float:
        if not self._items:
            return 0.0
        return round(promedio(r.descuento_general for r in self._items.values()), 2)

    def con_descuento_general_entre(self, minimo: float, maximo: float) -> List[ListaPrecio]:
        if minimo > maximo:
            minimo, maximo = maximo, minimo
        return [r for r in self.listar() if minimo <= r.descuento_general <= maximo]

    def mayores_por_descuento_general(self, n: int = 5) -> List[ListaPrecio]:
        return sorted(self._items.values(), key=lambda r: (-r.descuento_general, r.id))[:n]

    def por_vigente_desde_entre(self, inicio: str, fin: str) -> List[ListaPrecio]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.vigente_desde and inicio <= r.vigente_desde <= fin]

    def conteo_mensual_vigente_desde(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.vigente_desde:
                conteo[registro.vigente_desde[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_vigente_hasta_entre(self, inicio: str, fin: str) -> List[ListaPrecio]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.vigente_hasta and inicio <= r.vigente_hasta <= fin]

    def conteo_mensual_vigente_hasta(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.vigente_hasta:
                conteo[registro.vigente_hasta[:7]] += 1
        return dict(sorted(conteo.items()))

    def por_moneda(self, valor: str) -> List[ListaPrecio]:
        """Registros cuyo campo moneda es ``valor``."""
        if valor not in OPCIONES_LISTA_PRECIO_MONEDA:
            raise ValueError(f"moneda inválido: {valor!r}")
        return [r for r in self.listar() if r.moneda == valor]

    def conteo_por_moneda(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_LISTA_PRECIO_MONEDA}
        for registro in self._items.values():
            conteo[registro.moneda] += 1
        return conteo

    def buscar_texto(self, termino: str) -> List[ListaPrecio]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_tipo_cliente": self.conteo_por_tipo_cliente(),
            "por_moneda": self.conteo_por_moneda(),
        }


def reporte_listas_precios(repo: RepositorioListasPrecios, limite: int = 25) -> str:
    """Listado en texto plano de listas de precios."""
    encabezados = ['ID', 'Clave', 'Nombre', 'Tipo de cliente', 'Descuento %', 'Desde']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.clave,
            truncar(r.nombre, 28),
            r.tipo_cliente,
            f"{r.descuento_general:.2f}",
            r.vigente_desde,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Listas de precios ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_listas_precios_demo(n: int = 10, semilla: int = 32) -> List[ListaPrecio]:
    """Genera ``n`` registros de listas de precios reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[ListaPrecio] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["clave"] = f"LP{i:02d}"
        v["nombre"] = f"Lista {rng.choice(('General', 'Mayoreo', 'Institucional', 'Temporada', 'Empleados'))} {i}"
        v["tipo_cliente"] = rng.choice(OPCIONES_LISTA_PRECIO_TIPO_CLIENTE)
        v["descuento_general"] = round(rng.uniform(0, 25), 2)
        v["vigente_desde"] = fecha_aleatoria_demo(rng)
        v["vigente_hasta"] = sumar_dias_iso(v["vigente_desde"], rng.randint(30, 365)) if rng.random() < 0.7 else ""
        v["moneda"] = "MXN" if rng.random() < 0.9 else "USD"
        registros.append(ListaPrecio(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: ConteoInventario  (Conteos de inventario)
# ----------------------------------------------------------------------------

_PATRON_CONTEO_INVENTARIO_ALMACEN_CLAVE = re.compile(r"^ALM\d{2}$")
_PATRON_CONTEO_INVENTARIO_SKU = re.compile(r"^[A-Z]{3}-\d{5}$")


@dataclass
class ConteoInventario:
    """Conteo físico (cíclico) de un SKU en un almacén."""

    id: int
    almacen_clave: str
    sku: str
    fecha: str
    cantidad_sistema: int
    cantidad_contada: int
    contado_por: str
    validado: bool = False

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.almacen_clave, str) or not _PATRON_CONTEO_INVENTARIO_ALMACEN_CLAVE.match(self.almacen_clave):
            errores.append("almacen_clave tiene un formato inválido")
        if not isinstance(self.sku, str) or not _PATRON_CONTEO_INVENTARIO_SKU.match(self.sku):
            errores.append("sku tiene un formato inválido")
        if not es_fecha_iso(self.fecha):
            errores.append("fecha debe tener formato AAAA-MM-DD")
        if not isinstance(self.cantidad_sistema, int) or isinstance(self.cantidad_sistema, bool) or not 0 <= self.cantidad_sistema <= 100_000:
            errores.append("cantidad_sistema debe ser un entero entre 0 y 100_000")
        if not isinstance(self.cantidad_contada, int) or isinstance(self.cantidad_contada, bool) or not 0 <= self.cantidad_contada <= 100_000:
            errores.append("cantidad_contada debe ser un entero entre 0 y 100_000")
        if not isinstance(self.contado_por, str) or not self.contado_por.strip():
            errores.append("contado_por es obligatorio")
        elif len(self.contado_por) > 80:
            errores.append("contado_por excede 80 caracteres")
        if not isinstance(self.validado, bool):
            errores.append("validado debe ser booleano")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "ConteoInventario":
        return cls(
            id=int(datos["id"]),
            almacen_clave=str(datos["almacen_clave"]),
            sku=str(datos["sku"]),
            fecha=str(datos["fecha"]),
            cantidad_sistema=int(datos["cantidad_sistema"]),
            cantidad_contada=int(datos["cantidad_contada"]),
            contado_por=str(datos["contado_por"]),
            validado=a_booleano(datos.get("validado", False)),
        )

    def diferencia(self) -> int:
        return self.cantidad_contada - self.cantidad_sistema

    def exactitud_pct(self) -> float:
        if self.cantidad_sistema == 0:
            return 100.0 if self.cantidad_contada == 0 else 0.0
        return round(max(0.0, 1 - abs(self.diferencia()) / self.cantidad_sistema) * 100, 2)


class RepositorioConteosInventario(RepositorioMemoria):
    """Repositorio en memoria de conteos de inventario."""

    entidad = ConteoInventario
    nombre = "conteos_inventario"
    CAMPOS_TEXTO = ('contado_por',)

    def con_almacen_clave(self, valor: str) -> List[ConteoInventario]:
        return [r for r in self.listar() if r.almacen_clave == valor]

    def con_sku(self, valor: str) -> List[ConteoInventario]:
        return [r for r in self.listar() if r.sku == valor]

    def por_fecha_entre(self, inicio: str, fin: str) -> List[ConteoInventario]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.fecha and inicio <= r.fecha <= fin]

    def conteo_mensual_fecha(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.fecha:
                conteo[registro.fecha[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_cantidad_sistema_entre(self, minimo: int, maximo: int) -> List[ConteoInventario]:
        return [r for r in self.listar() if minimo <= r.cantidad_sistema <= maximo]

    def maximo_cantidad_sistema(self) -> Optional[int]:
        valores = [r.cantidad_sistema for r in self._items.values()]
        return max(valores) if valores else None

    def con_cantidad_contada_entre(self, minimo: int, maximo: int) -> List[ConteoInventario]:
        return [r for r in self.listar() if minimo <= r.cantidad_contada <= maximo]

    def maximo_cantidad_contada(self) -> Optional[int]:
        valores = [r.cantidad_contada for r in self._items.values()]
        return max(valores) if valores else None

    def donde_validado(self, valor: bool = True) -> List[ConteoInventario]:
        return [r for r in self.listar() if r.validado is valor]

    def buscar_texto(self, termino: str) -> List[ConteoInventario]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
        }

    def exactitud_global(self) -> float:
        if not self._items:
            return 100.0
        return round(promedio(c.exactitud_pct() for c in self._items.values()), 2)


def reporte_conteos_inventario(repo: RepositorioConteosInventario, limite: int = 25) -> str:
    """Listado en texto plano de conteos de inventario."""
    encabezados = ['ID', 'Almacén', 'SKU', 'Fecha', 'Sistema', 'Contado']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.almacen_clave,
            r.sku,
            r.fecha,
            r.cantidad_sistema,
            r.cantidad_contada,
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Conteos de inventario ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_conteos_inventario_demo(n: int = 10, semilla: int = 33) -> List[ConteoInventario]:
    """Genera ``n`` registros de conteos de inventario reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[ConteoInventario] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["almacen_clave"] = f"ALM{rng.randint(1, 15):02d}"
        v["sku"] = sku_demo(rng)
        v["fecha"] = fecha_aleatoria_demo(rng)
        v["cantidad_sistema"] = rng.randint(0, 800)
        v["cantidad_contada"] = max(0, v["cantidad_sistema"] + rng.choice((0, 0, 0, -1, -2, 1, -5)))
        v["contado_por"] = nombre_persona_demo(rng)
        v["validado"] = rng.random() < 0.5
        registros.append(ConteoInventario(**v))
    return registros


# ----------------------------------------------------------------------------
# Entidad: Usuario  (Usuarios)
# ----------------------------------------------------------------------------

_PATRON_USUARIO_USUARIO = re.compile(r"^[a-z][a-z0-9_]{3,19}$")
OPCIONES_USUARIO_ROL = ('admin', 'gerente', 'cajero', 'almacen', 'consulta')


@dataclass
class Usuario:
    """Usuario del sistema con su rol de acceso."""

    id: int
    usuario: str
    nombre_completo: str
    email: str
    rol: str
    activo: bool = True
    ultimo_acceso: str = ''
    intentos_fallidos: int = 0

    def validar(self) -> List[str]:
        """Regresa la lista de errores de validación (vacía si el registro es válido)."""
        errores: List[str] = []
        if not isinstance(self.id, int) or isinstance(self.id, bool) or self.id <= 0:
            errores.append("id debe ser un entero positivo")
        if not isinstance(self.usuario, str) or not _PATRON_USUARIO_USUARIO.match(self.usuario):
            errores.append("usuario tiene un formato inválido")
        if not isinstance(self.nombre_completo, str) or not self.nombre_completo.strip():
            errores.append("nombre_completo es obligatorio")
        elif len(self.nombre_completo) > 120:
            errores.append("nombre_completo excede 120 caracteres")
        if not es_email_valido(self.email):
            errores.append("email no es un correo válido")
        if self.rol not in OPCIONES_USUARIO_ROL:
            errores.append(f"rol debe ser uno de: {', '.join(OPCIONES_USUARIO_ROL)}")
        if not isinstance(self.activo, bool):
            errores.append("activo debe ser booleano")
        if self.ultimo_acceso and not es_fecha_iso(self.ultimo_acceso):
            errores.append("ultimo_acceso debe tener formato AAAA-MM-DD")
        if not isinstance(self.intentos_fallidos, int) or isinstance(self.intentos_fallidos, bool) or not 0 <= self.intentos_fallidos <= 10:
            errores.append("intentos_fallidos debe ser un entero entre 0 y 10")
        return errores

    def es_valido(self) -> bool:
        return not self.validar()

    def a_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def desde_dict(cls, datos: Dict[str, Any]) -> "Usuario":
        return cls(
            id=int(datos["id"]),
            usuario=str(datos["usuario"]),
            nombre_completo=str(datos["nombre_completo"]),
            email=str(datos["email"]),
            rol=str(datos["rol"]),
            activo=a_booleano(datos.get("activo", True)),
            ultimo_acceso=str(datos.get("ultimo_acceso", '')),
            intentos_fallidos=int(datos.get("intentos_fallidos", 0)),
        )

    def bloqueado(self, max_intentos: int = 5) -> bool:
        return self.intentos_fallidos >= max_intentos


class RepositorioUsuarios(RepositorioMemoria):
    """Repositorio en memoria de usuarios."""

    entidad = Usuario
    nombre = "usuarios"
    CAMPOS_TEXTO = ('nombre_completo',)

    def con_usuario(self, valor: str) -> List[Usuario]:
        return [r for r in self.listar() if r.usuario == valor]

    def por_rol(self, valor: str) -> List[Usuario]:
        """Registros cuyo campo rol es ``valor``."""
        if valor not in OPCIONES_USUARIO_ROL:
            raise ValueError(f"rol inválido: {valor!r}")
        return [r for r in self.listar() if r.rol == valor]

    def conteo_por_rol(self) -> Dict[str, int]:
        conteo = {opcion: 0 for opcion in OPCIONES_USUARIO_ROL}
        for registro in self._items.values():
            conteo[registro.rol] += 1
        return conteo

    def donde_activo(self, valor: bool = True) -> List[Usuario]:
        return [r for r in self.listar() if r.activo is valor]

    def por_ultimo_acceso_entre(self, inicio: str, fin: str) -> List[Usuario]:
        """Filtra por rango de fechas ISO (ambos extremos inclusive)."""
        return [r for r in self.listar() if r.ultimo_acceso and inicio <= r.ultimo_acceso <= fin]

    def conteo_mensual_ultimo_acceso(self) -> Dict[str, int]:
        conteo: Dict[str, int] = defaultdict(int)
        for registro in self._items.values():
            if registro.ultimo_acceso:
                conteo[registro.ultimo_acceso[:7]] += 1
        return dict(sorted(conteo.items()))

    def con_intentos_fallidos_entre(self, minimo: int, maximo: int) -> List[Usuario]:
        return [r for r in self.listar() if minimo <= r.intentos_fallidos <= maximo]

    def maximo_intentos_fallidos(self) -> Optional[int]:
        valores = [r.intentos_fallidos for r in self._items.values()]
        return max(valores) if valores else None

    def buscar_texto(self, termino: str) -> List[Usuario]:
        """Búsqueda sin acentos ni mayúsculas en los campos de texto."""
        objetivo = quitar_acentos(termino).lower().strip()
        if not objetivo:
            return self.listar()
        return [
            r for r in self.listar()
            if any(objetivo in quitar_acentos(str(getattr(r, campo))).lower() for campo in self.CAMPOS_TEXTO)
        ]

    def resumen(self) -> Dict[str, Any]:
        return {
            "total": len(self),
            "por_rol": self.conteo_por_rol(),
        }


def reporte_usuarios(repo: RepositorioUsuarios, limite: int = 25) -> str:
    """Listado en texto plano de usuarios."""
    encabezados = ['ID', 'Usuario', 'Nombre', 'Correo', 'Rol', 'Activo']
    filas = []
    for r in repo.listar()[:limite]:
        filas.append([
            r.id,
            r.usuario,
            truncar(r.nombre_completo, 28),
            r.email,
            r.rol,
            "Sí" if r.activo else "No",
        ])
    pie = "" if len(repo) <= limite else f"\n... y {len(repo) - limite} registros más"
    return f"Usuarios ({len(repo)} registros)\n" + tabla_texto(encabezados, filas) + pie


def generar_usuarios_demo(n: int = 10, semilla: int = 34) -> List[Usuario]:
    """Genera ``n`` registros de usuarios reproducibles para pruebas y demostraciones."""
    rng = random.Random(semilla)
    registros: List[Usuario] = []
    for i in range(1, n + 1):
        v: Dict[str, Any] = {"id": i}
        v["usuario"] = slugify(rng.choice(NOMBRES_DEMO)).replace("-", "_")[:12] + f"_{i:02d}"
        v["nombre_completo"] = nombre_persona_demo(rng)
        v["email"] = email_demo(rng)
        v["rol"] = rng.choice(OPCIONES_USUARIO_ROL)
        v["activo"] = rng.random() < 0.9
        v["ultimo_acceso"] = fecha_aleatoria_demo(rng, date(2026, 1, 1), date(2026, 11, 15)) if rng.random() < 0.85 else ""
        v["intentos_fallidos"] = rng.choice((0, 0, 0, 1, 2, 5))
        registros.append(Usuario(**v))
    return registros


CATALOGO_ENTIDADES: Dict[str, Tuple[type, type, Callable[..., List[Any]]]] = {
    "proveedores": (Proveedor, RepositorioProveedores, generar_proveedores_demo),
    "categorias": (Categoria, RepositorioCategorias, generar_categorias_demo),
    "productos": (Producto, RepositorioProductos, generar_productos_demo),
    "sucursales": (Sucursal, RepositorioSucursales, generar_sucursales_demo),
    "empleados": (Empleado, RepositorioEmpleados, generar_empleados_demo),
    "clientes": (Cliente, RepositorioClientes, generar_clientes_demo),
    "promociones": (Promocion, RepositorioPromociones, generar_promociones_demo),
    "cupones": (Cupon, RepositorioCupones, generar_cupones_demo),
    "pedidos": (Pedido, RepositorioPedidos, generar_pedidos_demo),
    "envios": (Envio, RepositorioEnvios, generar_envios_demo),
    "devoluciones": (Devolucion, RepositorioDevoluciones, generar_devoluciones_demo),
    "almacenes": (Almacen, RepositorioAlmacenes, generar_almacenes_demo),
    "vehiculos": (Vehiculo, RepositorioVehiculos, generar_vehiculos_demo),
    "rutas": (Ruta, RepositorioRutas, generar_rutas_demo),
    "turnos": (Turno, RepositorioTurnos, generar_turnos_demo),
    "ventas_registradas": (VentaRegistrada, RepositorioVentasRegistradas, generar_ventas_registradas_demo),
    "cortes_caja": (CorteCaja, RepositorioCortesCaja, generar_cortes_caja_demo),
    "auditorias": (Auditoria, RepositorioAuditorias, generar_auditorias_demo),
    "mantenimientos": (Mantenimiento, RepositorioMantenimientos, generar_mantenimientos_demo),
    "gastos": (Gasto, RepositorioGastos, generar_gastos_demo),
    "quejas": (Queja, RepositorioQuejas, generar_quejas_demo),
    "listas_precios": (ListaPrecio, RepositorioListasPrecios, generar_listas_precios_demo),
    "conteos_inventario": (ConteoInventario, RepositorioConteosInventario, generar_conteos_inventario_demo),
    "usuarios": (Usuario, RepositorioUsuarios, generar_usuarios_demo),
}


# ==============================================================================
# SECCIÓN 15. INVENTARIO
# ==============================================================================

TIPOS_MOVIMIENTO = ("entrada", "salida", "ajuste")
_PATRON_SKU = re.compile(r"^[A-Z]{3}-\d{5}$")


@dataclass
class MovimientoInventario:
    fecha: date
    sku: str
    tipo: str
    cantidad: int
    costo_unitario: float = 0.0
    referencia: str = ""

    def __post_init__(self) -> None:
        if self.tipo not in TIPOS_MOVIMIENTO:
            raise ErrorValidacion("MovimientoInventario", [f"tipo inválido: {self.tipo}"])


class Inventario:
    """Control de existencias con costo promedio ponderado."""

    def __init__(self) -> None:
        self._productos: Dict[str, Dict[str, Any]] = {}
        self._existencias: Dict[str, int] = {}
        self._costo_promedio: Dict[str, float] = {}
        self.movimientos: List[MovimientoInventario] = []

    def dar_de_alta(self, sku: str, descripcion: str, precio_venta: float, costo: float,
                    minimo: int = 0, categoria: str = "general") -> Dict[str, Any]:
        errores = []
        if not _PATRON_SKU.match(sku or ""):
            errores.append(f"SKU con formato inválido: {sku!r}")
        if precio_venta < 0:
            errores.append("el precio de venta no puede ser negativo")
        if costo < 0:
            errores.append("el costo no puede ser negativo")
        if minimo < 0:
            errores.append("la existencia mínima no puede ser negativa")
        if errores:
            raise ErrorValidacion("Producto", errores)
        if sku in self._productos:
            raise ErrorSistema(f"SKU duplicado: {sku}")
        self._productos[sku] = {
            "sku": sku,
            "descripcion": descripcion,
            "precio_venta": float(precio_venta),
            "costo": float(costo),
            "minimo": minimo,
            "categoria": categoria,
        }
        self._existencias[sku] = 0
        self._costo_promedio[sku] = float(costo)
        return self._productos[sku]

    def producto(self, sku: str) -> Dict[str, Any]:
        try:
            return self._productos[sku]
        except KeyError:
            raise EntidadNoEncontrada(f"el producto {sku} no existe") from None

    def existencia(self, sku: str) -> int:
        self.producto(sku)
        return self._existencias[sku]

    def costo_promedio(self, sku: str) -> float:
        self.producto(sku)
        return round(self._costo_promedio[sku], 4)

    def registrar_entrada(self, sku: str, cantidad: int, costo_unitario: float,
                          fecha: Optional[date] = None, referencia: str = "") -> None:
        self.producto(sku)
        if cantidad <= 0:
            raise ErrorValidacion("Entrada", ["la cantidad debe ser positiva"])
        if costo_unitario < 0:
            raise ErrorValidacion("Entrada", ["el costo unitario no puede ser negativo"])
        existencia_actual = self._existencias[sku]
        costo_actual = self._costo_promedio[sku]
        nueva_existencia = existencia_actual + cantidad
        self._costo_promedio[sku] = (
            existencia_actual * costo_actual + cantidad * costo_unitario
        ) / nueva_existencia
        self._existencias[sku] = nueva_existencia
        self.movimientos.append(
            MovimientoInventario(fecha or date.today(), sku, "entrada", cantidad, costo_unitario, referencia)
        )

    def registrar_salida(self, sku: str, cantidad: int, fecha: Optional[date] = None, referencia: str = "") -> None:
        self.producto(sku)
        if cantidad <= 0:
            raise ErrorValidacion("Salida", ["la cantidad debe ser positiva"])
        disponible = self._existencias[sku]
        if cantidad > disponible:
            raise StockInsuficiente(sku, cantidad, disponible)
        self._existencias[sku] = disponible - cantidad
        self.movimientos.append(
            MovimientoInventario(fecha or date.today(), sku, "salida", cantidad, self._costo_promedio[sku], referencia)
        )

    def ajustar(self, sku: str, conteo_fisico: int, fecha: Optional[date] = None, motivo: str = "conteo cíclico") -> int:
        self.producto(sku)
        if conteo_fisico < 0:
            raise ErrorValidacion("Ajuste", ["el conteo físico no puede ser negativo"])
        diferencia = conteo_fisico - self._existencias[sku]
        if diferencia == 0:
            return 0
        self._existencias[sku] = conteo_fisico
        self.movimientos.append(
            MovimientoInventario(fecha or date.today(), sku, "ajuste", diferencia, self._costo_promedio[sku], motivo)
        )
        return diferencia

    def valor_inventario(self) -> float:
        return round(sum(self._existencias[s] * self._costo_promedio[s] for s in self._productos), 2)

    def productos_bajo_minimo(self) -> List[str]:
        return sorted(s for s, p in self._productos.items() if self._existencias[s] < p["minimo"])

    def productos_por_categoria(self) -> Dict[str, List[str]]:
        agrupados = agrupar_por(self._productos.values(), lambda p: p["categoria"])
        return {cat: sorted(p["sku"] for p in prods) for cat, prods in sorted(agrupados.items())}

    def skus_ordenados(self) -> List[str]:
        return sorted(self._productos)

    def buscar_sku(self, sku: str) -> bool:
        """Búsqueda rápida sobre el catálogo ordenado (usada por el punto de venta)."""
        return busqueda_binaria(self.skus_ordenados(), sku) >= 0

    def movimientos_de(self, sku: str) -> List[MovimientoInventario]:
        return [m for m in self.movimientos if m.sku == sku]

    def rotacion(self, sku: str) -> float:
        salidas = sum(m.cantidad for m in self.movimientos_de(sku) if m.tipo == "salida")
        existencia = self.existencia(sku)
        if existencia == 0:
            return math.inf if salidas else 0.0
        return round(salidas / existencia, 2)

    def kardex(self, sku: str) -> List[Dict[str, Any]]:
        return construir_kardex(self.movimientos_de(sku))

    def __len__(self) -> int:
        return len(self._productos)


def construir_kardex(movimientos: Iterable[MovimientoInventario], saldo_inicial: int = 0,
                     kardex: List[Dict[str, Any]] = []) -> List[Dict[str, Any]]:
    """Construye la tarjeta kárdex (movimientos con saldo acumulado).

    Si se proporciona ``kardex`` los renglones se agregan a esa lista; de lo contrario
    se crea una lista nueva.
    """
    kardex = [] if kardex is None else kardex
    saldo = saldo_inicial
    for movimiento in movimientos:
        if movimiento.tipo == "entrada":
            saldo += movimiento.cantidad
        elif movimiento.tipo == "salida":
            saldo -= movimiento.cantidad
        elif movimiento.tipo == "ajuste":
            saldo += movimiento.cantidad
        else:
            raise ErrorValidacion("Kardex", [f"tipo de movimiento desconocido: {movimiento.tipo}"])
        kardex.append({
            "fecha": movimiento.fecha.isoformat(),
            "sku": movimiento.sku,
            "tipo": movimiento.tipo,
            "cantidad": movimiento.cantidad,
            "saldo": saldo,
            "referencia": movimiento.referencia,
        })
    return kardex


# ==============================================================================
# SECCIÓN 16. PRECIOS, DESCUENTOS Y ENVÍOS
# ==============================================================================

ESCALONES_MAYOREO = ((12, 5.0), (48, 10.0), (120, 15.0))


def aplicar_descuento(precio: float, porcentaje: float) -> float:
    """Aplica un descuento porcentual a un precio y redondea a centavos.

    Ejemplo: aplicar_descuento(200, 10) -> 180.0
    """
    if precio < 0:
        raise ValueError("el precio no puede ser negativo")
    if not 0 <= porcentaje <= 100:
        raise ValueError(f"porcentaje fuera de rango: {porcentaje}")
    return round(precio * (1 - porcentaje) / 100, 2)


def precio_con_iva(precio_sin_iva: float, tasa: float = TASA_IVA) -> float:
    return redondear_moneda(precio_sin_iva * (1 + tasa))


def desglosar_iva(precio_con_iva_incluido: float, tasa: float = TASA_IVA) -> Dict[str, float]:
    base = precio_con_iva_incluido / (1 + tasa)
    return {"base": round(base, 2), "iva": round(precio_con_iva_incluido - base, 2)}


def precio_mayoreo(precio_lista: float, cantidad: int,
                   escalones: Sequence[Tuple[int, float]] = ESCALONES_MAYOREO) -> float:
    """Precio unitario según la cantidad comprada."""
    descuento = 0.0
    for minimo, porcentaje in escalones:
        if cantidad >= minimo:
            descuento = porcentaje
    return aplicar_descuento(precio_lista, descuento)


def aplicar_promocion_nxm(cantidad: int, precio_unitario: float, n: int = 3, m: int = 2) -> float:
    """Promoción 'lleva n paga m' (por ejemplo 3x2)."""
    if not 0 < m <= n:
        raise ValueError("se requiere 0 < m <= n")
    grupos, sueltos = divmod(cantidad, n)
    return round((grupos * m + sueltos) * precio_unitario, 2)


def margen_bruto(precio: float, costo: float) -> float:
    """Margen bruto como porcentaje del precio."""
    if precio == 0:
        return 0.0
    return round((precio - costo) / precio * 100, 2)


def markup(precio: float, costo: float) -> float:
    """Sobreprecio como porcentaje del costo."""
    if costo == 0:
        raise ValueError("el costo no puede ser cero")
    return round((precio - costo) / costo * 100, 2)


ZONAS_ENVIO = (
    ("44", "ZMG"), ("45", "ZMG"), ("46", "Jalisco interior"), ("47", "Altos"),
    ("36", "Bajío"), ("37", "Bajío"), ("38", "Bajío"), ("58", "Michoacán"),
    ("20", "Aguascalientes"), ("76", "Querétaro"),
)
TARIFAS_ZONA: Dict[str, Tuple[float, float]] = {
    "ZMG": (60.0, 4.5),
    "Jalisco interior": (120.0, 6.0),
    "Altos": (110.0, 5.5),
    "Bajío": (140.0, 6.5),
    "Michoacán": (150.0, 7.0),
    "Aguascalientes": (150.0, 7.0),
    "Querétaro": (170.0, 7.5),
    "Nacional": (250.0, 9.5),
}


@memoizar(capacidad=64)
def zona_por_codigo_postal(codigo_postal: str) -> str:
    if not (isinstance(codigo_postal, str) and len(codigo_postal) == 5 and codigo_postal.isdigit()):
        raise ValueError(f"código postal inválido: {codigo_postal!r}")
    for prefijo, zona in ZONAS_ENVIO:
        if codigo_postal.startswith(prefijo):
            return zona
    return "Nacional"


def costo_envio(codigo_postal: str, peso_kg: float) -> float:
    if peso_kg <= 0:
        raise ValueError("el peso debe ser positivo")
    base, por_kg = TARIFAS_ZONA[zona_por_codigo_postal(codigo_postal)]
    return redondear_moneda(base + por_kg * math.ceil(peso_kg))


# ==============================================================================
# SECCIÓN 17. PUNTO DE VENTA
# ==============================================================================


class GeneradorFolios:
    def __init__(self, prefijo: str, inicio: int = 1, digitos: int = 6):
        self.prefijo = prefijo
        self.digitos = digitos
        self._contador = itertools.count(inicio)
        self.emitidos: List[str] = []

    def siguiente(self) -> str:
        folio = f"{self.prefijo}-{next(self._contador):0{self.digitos}d}"
        self.emitidos.append(folio)
        return folio


def crear_linea_venta(sku: str, descripcion: str, cantidad: int, precio_unitario: float,
                      descuento_pct: float = 0.0) -> Dict[str, Any]:
    if cantidad <= 0:
        raise ErrorValidacion("LineaVenta", ["la cantidad debe ser positiva"])
    if precio_unitario < 0:
        raise ErrorValidacion("LineaVenta", ["el precio no puede ser negativo"])
    return {
        "sku": sku,
        "descripcion": descripcion,
        "cantidad": cantidad,
        "precio_unitario": float(precio_unitario),
        "descuento_pct": float(descuento_pct),
    }


def importe_linea(linea: Dict[str, Any]) -> float:
    bruto = linea["cantidad"] * linea["precio_unitario"]
    return round(bruto * (1 - linea["descuento_pct"] / 100), 2)


def calcular_subtotal_venta(lineas: Iterable[Dict[str, Any]]) -> float:
    """Suma de (precio neto unitario x cantidad) de todas las líneas."""
    subtotal = 0.0
    for linea in lineas:
        precio_neto = aplicar_descuento(linea["precio"], linea["descuento_pct"])
        subtotal += precio_neto * linea["cantidad"]
    return redondear_moneda(subtotal)


class Carrito:
    def __init__(self, inventario: Inventario, cliente_id: Optional[int] = None):
        self.inventario = inventario
        self.cliente_id = cliente_id
        self.lineas: List[Dict[str, Any]] = []

    def agregar(self, sku: str, cantidad: int = 1, descuento_pct: float = 0.0) -> Dict[str, Any]:
        producto = self.inventario.producto(sku)
        for linea in self.lineas:
            if linea["sku"] == sku and linea["descuento_pct"] == descuento_pct:
                linea["cantidad"] += cantidad
                return linea
        linea = crear_linea_venta(sku, producto["descripcion"], cantidad, producto["precio_venta"], descuento_pct)
        self.lineas.append(linea)
        return linea

    def quitar(self, sku: str) -> int:
        antes = len(self.lineas)
        self.lineas = [l for l in self.lineas if l["sku"] != sku]
        return antes - len(self.lineas)

    def total_articulos(self) -> int:
        return sum(l["cantidad"] for l in self.lineas)

    def subtotal(self) -> float:
        return calcular_subtotal_venta(self.lineas)

    def vaciar(self) -> None:
        self.lineas = []

    def __len__(self) -> int:
        return len(self.lineas)


FORMAS_PAGO = ("efectivo", "tarjeta_debito", "tarjeta_credito", "transferencia", "vales")


def procesar_venta(carrito: Carrito, folios: GeneradorFolios, fecha: Optional[date] = None,
                   tipo_cliente: str = "persona_fisica", forma_pago: str = "efectivo",
                   pago_recibido: Optional[float] = None) -> Dict[str, Any]:
    """Valida existencias, calcula impuestos, descarga inventario y regresa la venta."""
    if not carrito.lineas:
        raise ErrorValidacion("Venta", ["el carrito está vacío"])
    if forma_pago not in FORMAS_PAGO:
        raise ErrorValidacion("Venta", [f"forma de pago inválida: {forma_pago}"])
    requeridos: Dict[str, int] = defaultdict(int)
    for linea in carrito.lineas:
        requeridos[linea["sku"]] += linea["cantidad"]
    for sku, cantidad in requeridos.items():
        disponible = carrito.inventario.existencia(sku)
        if cantidad > disponible:
            raise StockInsuficiente(sku, cantidad, disponible)
    subtotal = carrito.subtotal()
    impuestos = calcular_impuestos_factura(subtotal, tipo_cliente)
    folio = folios.siguiente()
    fecha = fecha or date.today()
    for linea in carrito.lineas:
        carrito.inventario.registrar_salida(linea["sku"], linea["cantidad"], fecha, referencia=folio)
    cambio = None
    if forma_pago == "efectivo":
        if pago_recibido is None:
            pago_recibido = impuestos["total"]
        if pago_recibido < impuestos["total"]:
            raise ErrorValidacion("Venta", ["el pago recibido es insuficiente"])
        cambio = redondear_moneda(pago_recibido - impuestos["total"])
    venta = {
        "folio": folio,
        "fecha": fecha.isoformat(),
        "cliente_id": carrito.cliente_id,
        "lineas": [dict(l) for l in carrito.lineas],
        "forma_pago": forma_pago,
        "pago_recibido": pago_recibido,
        "cambio": cambio,
    }
    venta.update(impuestos)
    carrito.vaciar()
    return venta


def desglosar_cambio(cambio: float, denominaciones: Sequence[float] = DENOMINACIONES_MXN) -> Tuple[Dict[float, int], float]:
    """Desglosa el cambio en billetes y monedas. Regresa (desglose, residuo no entregable)."""
    centavos = int(round(cambio * 100))
    if centavos < 0:
        raise ValueError("el cambio no puede ser negativo")
    desglose: Dict[float, int] = {}
    for denominacion in denominaciones:
        valor = int(round(denominacion * 100))
        cantidad, centavos = divmod(centavos, valor)
        if cantidad:
            desglose[denominacion] = cantidad
    return desglose, centavos / 100


def generar_ticket(venta: Dict[str, Any], ancho: int = 42) -> str:
    lineas = [
        NOMBRE_EMPRESA.center(ancho),
        f"RFC: {RFC_EMPRESA}".center(ancho),
        "=" * ancho,
        f"Folio: {venta['folio']}",
        f"Fecha: {venta['fecha']}",
        "-" * ancho,
    ]
    ancho_descripcion = ancho - 16
    for linea in venta["lineas"]:
        importe = importe_linea(linea)
        descripcion = truncar(linea["descripcion"], ancho_descripcion)
        lineas.append(f"{linea['cantidad']:>3} {descripcion:<{ancho_descripcion}}{formatear_moneda(importe):>12}")
        if linea["descuento_pct"]:
            lineas.append(f"    descuento {linea['descuento_pct']:.0f}%")
    lineas.append("-" * ancho)
    conceptos = (
        ("Subtotal", "subtotal"), ("IEPS", "ieps"), ("IVA", "iva"),
        ("Ret. ISR", "retencion_isr"), ("Ret. IVA", "retencion_iva"), ("TOTAL", "total"),
    )
    for etiqueta, clave in conceptos:
        valor = venta.get(clave, 0.0)
        if clave in ("ieps", "retencion_isr", "retencion_iva") and not valor:
            continue
        lineas.append(f"{etiqueta:>{ancho - 14}}{formatear_moneda(valor):>14}")
    if venta.get("cambio") is not None:
        lineas.append(f"{'Su pago':>{ancho - 14}}{formatear_moneda(venta['pago_recibido']):>14}")
        lineas.append(f"{'Cambio':>{ancho - 14}}{formatear_moneda(venta['cambio']):>14}")
    lineas.append("")
    lineas.extend(textwrap.wrap(monto_a_letras(venta["total"]), ancho))
    lineas.append(CONFIGURACION_POR_DEFECTO["ticket"]["leyenda"].center(ancho))
    return "\n".join(lineas)


# ==============================================================================
# SECCIÓN 18. FACTURACIÓN
# ==============================================================================

FORMAS_PAGO_SAT = {"01": "Efectivo", "03": "Transferencia", "04": "Tarjeta de crédito", "28": "Tarjeta de débito", "99": "Por definir"}
METODOS_PAGO_SAT = ("PUE", "PPD")


def calcular_impuestos_factura(subtotal: float, tipo_cliente: str = "persona_fisica",
                               base_ieps: float = 0.0) -> Dict[str, float]:
    """Calcula IEPS, IVA, retenciones y total.

    Régimen simplificado de confianza (RESICO): cuando el receptor es persona moral
    se retiene 1.25% de ISR y dos terceras partes del IVA trasladado.
    """
    if subtotal < 0:
        raise ErrorValidacion("Factura", ["el subtotal no puede ser negativo"])
    if base_ieps > subtotal + 0.005:
        raise ErrorValidacion("Factura", ["la base de IEPS no puede exceder el subtotal"])
    subtotal = redondear_moneda(subtotal)
    ieps = redondear_moneda(base_ieps * TASA_IEPS_BEBIDAS)
    iva = redondear_moneda((subtotal + ieps) * TASA_IVA)
    retencion_isr = 0.0
    retencion_iva = 0.0
    if tipo_cliente == "persona_moral":
        retencion_isr = redondear_moneda(subtotal * TASA_RETENCION_ISR)
        retencion_iva = redondear_moneda(iva_trasladado * FACTOR_RETENCION_IVA)
    elif tipo_cliente != "persona_fisica":
        raise ErrorValidacion("Factura", [f"tipo de cliente desconocido: {tipo_cliente}"])
    total = redondear_moneda(subtotal + ieps + iva - retencion_isr - retencion_iva)
    return {
        "subtotal": subtotal,
        "ieps": ieps,
        "iva": iva,
        "retencion_isr": retencion_isr,
        "retencion_iva": retencion_iva,
        "total": total,
    }


@dataclass
class ConceptoFactura:
    clave_producto: str
    descripcion: str
    cantidad: float
    valor_unitario: float
    aplica_ieps: bool = False

    def importe(self) -> float:
        return redondear_moneda(self.cantidad * self.valor_unitario)


@dataclass
class Factura:
    serie: str
    folio: int
    fecha: date
    rfc_emisor: str
    rfc_receptor: str
    nombre_receptor: str
    conceptos: List[ConceptoFactura] = field(default_factory=list)
    forma_pago: str = "01"
    metodo_pago: str = "PUE"

    def validar(self) -> List[str]:
        errores = []
        if not es_rfc_valido(self.rfc_emisor):
            errores.append("RFC del emisor inválido")
        if not es_rfc_valido(self.rfc_receptor):
            errores.append("RFC del receptor inválido")
        if not self.conceptos:
            errores.append("la factura debe tener al menos un concepto")
        for i, concepto in enumerate(self.conceptos, start=1):
            if concepto.cantidad <= 0:
                errores.append(f"concepto {i}: la cantidad debe ser positiva")
            if concepto.valor_unitario < 0:
                errores.append(f"concepto {i}: el valor unitario no puede ser negativo")
        if self.forma_pago not in FORMAS_PAGO_SAT:
            errores.append(f"forma de pago no reconocida: {self.forma_pago}")
        if self.metodo_pago not in METODOS_PAGO_SAT:
            errores.append(f"método de pago no reconocido: {self.metodo_pago}")
        if self.metodo_pago == "PPD" and self.forma_pago != "99":
            errores.append("con método PPD la forma de pago debe ser 99 (por definir)")
        return errores

    def agregar_concepto(self, concepto: ConceptoFactura) -> None:
        self.conceptos.append(concepto)

    def subtotal(self) -> float:
        return redondear_moneda(sum(c.importe() for c in self.conceptos))

    def base_ieps(self) -> float:
        return redondear_moneda(sum(c.importe() for c in self.conceptos if c.aplica_ieps))

    def totales(self) -> Dict[str, float]:
        return calcular_impuestos_factura(self.subtotal(), tipo_persona_por_rfc(self.rfc_receptor), self.base_ieps())

    def folio_completo(self) -> str:
        return f"{self.serie}-{self.folio:07d}"

    def a_texto(self) -> str:
        totales = self.totales()
        filas = [
            [c.clave_producto, truncar(c.descripcion, 30), c.cantidad, formatear_moneda(c.valor_unitario), formatear_moneda(c.importe())]
            for c in self.conceptos
        ]
        partes = [
            encabezado_reporte(f"FACTURA {self.folio_completo()}"),
            f"Emisor:   {self.rfc_emisor}",
            f"Receptor: {self.rfc_receptor} - {self.nombre_receptor}",
            f"Fecha:    {self.fecha.isoformat()}   Forma de pago: {FORMAS_PAGO_SAT.get(self.forma_pago, '?')}   Método: {self.metodo_pago}",
            "",
            tabla_texto(["Clave", "Descripción", "Cant.", "P. unitario", "Importe"], filas),
            "",
        ]
        for etiqueta, clave in (("Subtotal", "subtotal"), ("IEPS", "ieps"), ("IVA 16%", "iva"),
                                ("Retención ISR", "retencion_isr"), ("Retención IVA", "retencion_iva"), ("Total", "total")):
            partes.append(f"{etiqueta:>60}: {formatear_moneda(totales[clave]):>15}")
        partes.append("")
        partes.append(monto_a_letras(totales["total"]))
        return "\n".join(partes)


# ==============================================================================
# SECCIÓN 19. NÓMINA
# ==============================================================================

# (límite inferior, cuota fija, % sobre excedente) - tarifa mensual art. 96 LISR
TABLA_ISR_MENSUAL: Tuple[Tuple[float, float, float], ...] = (
    (0.01, 0.00, 1.92),
    (746.05, 14.32, 6.40),
    (6332.06, 371.83, 10.88),
    (11128.02, 893.63, 16.00),
    (12935.83, 1182.88, 17.92),
    (15487.72, 1640.18, 21.36),
    (31236.50, 5004.12, 23.52),
    (49233.01, 9236.89, 30.00),
    (93993.91, 22665.17, 32.00),
    (125325.21, 32691.18, 34.00),
    (375975.62, 117912.32, 35.00),
)
_LIMITES_ISR = [fila[0] for fila in TABLA_ISR_MENSUAL]


def calcular_isr_mensual(ingreso_gravable: float) -> float:
    if ingreso_gravable < TABLA_ISR_MENSUAL[0][0]:
        return 0.0
    indice = bisect.bisect_right(_LIMITES_ISR, ingreso_gravable) - 1
    limite_inferior, cuota_fija, porcentaje = TABLA_ISR_MENSUAL[indice]
    return round(cuota_fija + (ingreso_gravable - limite_inferior) * porcentaje / 100, 2)


def cuota_imss_obrera(salario_mensual: float) -> float:
    """Aproximación de las cuotas obreras al IMSS (enfermedad, invalidez, cesantía)."""
    sbc_diario = salario_mensual / DIAS_MES_NOMINA
    excedente = max(0.0, sbc_diario - 3 * UMA_DIARIA)
    cuota_diaria = excedente * 0.004 + sbc_diario * (0.0025 + 0.00375 + 0.00625 + 0.01125)
    return round(cuota_diaria * DIAS_MES_NOMINA, 2)


def calcular_recibo_nomina(nombre: str, salario_mensual: float, horas_extra: float = 0, faltas: int = 0) -> Dict[str, Any]:
    if salario_mensual <= 0:
        raise ErrorValidacion("Nómina", ["el salario debe ser positivo"])
    salario_diario = salario_mensual / DIAS_MES_NOMINA
    descuento_faltas = round(salario_diario * faltas, 2)
    pago_extra = round(salario_diario / 8 * 2 * horas_extra, 2)
    percepciones = round(salario_mensual - descuento_faltas + pago_extra, 2)
    isr = calcular_isr_mensual(percepciones)
    subsidio = SUBSIDIO_EMPLEO_MONTO if percepciones <= SUBSIDIO_EMPLEO_LIMITE else 0.0
    isr_retenido = max(0.0, round(isr - subsidio, 2))
    imss = cuota_imss_obrera(salario_mensual)
    neto = round(percepciones - isr_retenido - imss, 2)
    return {
        "nombre": nombre,
        "salario_mensual": round(salario_mensual, 2),
        "descuento_faltas": descuento_faltas,
        "pago_horas_extra": pago_extra,
        "percepciones": percepciones,
        "isr": isr,
        "subsidio_empleo": subsidio,
        "isr_retenido": isr_retenido,
        "imss": imss,
        "neto": neto,
    }


def calcular_nomina(empleados: Iterable[Dict[str, Any]]) -> Dict[str, Any]:
    recibos = [
        calcular_recibo_nomina(e["nombre"], e["salario_mensual"], e.get("horas_extra", 0), e.get("faltas", 0))
        for e in empleados
    ]
    return {
        "recibos": recibos,
        "total_percepciones": round(sum(r["percepciones"] for r in recibos), 2),
        "total_isr": round(sum(r["isr_retenido"] for r in recibos), 2),
        "total_imss": round(sum(r["imss"] for r in recibos), 2),
        "total_neto": round(sum(r["neto"] for r in recibos), 2),
    }


def dias_vacaciones(anios_servicio: int) -> int:
    """Días de vacaciones según la reforma de 2023 a la LFT."""
    if anios_servicio < 1:
        return 0
    if anios_servicio <= 5:
        return 12 + 2 * (anios_servicio - 1)
    return 20 + 2 * ((anios_servicio - 6) // 5 + 1)


def aguinaldo(salario_diario: float, dias_trabajados_anio: int, dias_aguinaldo: int = 15) -> float:
    proporcion = min(dias_trabajados_anio, 365) / 365
    return round(salario_diario * dias_aguinaldo * proporcion, 2)


def prima_vacacional(salario_diario: float, anios_servicio: int, porcentaje: float = 25.0) -> float:
    return round(salario_diario * dias_vacaciones(anios_servicio) * porcentaje / 100, 2)


# ==============================================================================
# SECCIÓN 20. GRAFOS Y RUTAS DE REPARTO
# ==============================================================================


class Grafo:
    """Grafo ponderado (dirigido o no) representado con listas de adyacencia."""

    def __init__(self, dirigido: bool = False):
        self.dirigido = dirigido
        self._adyacencia: Dict[str, Dict[str, float]] = {}

    def agregar_nodo(self, nodo: str) -> None:
        self._adyacencia.setdefault(nodo, {})

    def agregar_arista(self, origen: str, destino: str, peso: float = 1.0) -> None:
        if peso < 0:
            raise ErrorRuta("no se admiten pesos negativos")
        self.agregar_nodo(origen)
        self.agregar_nodo(destino)
        self._adyacencia[origen][destino] = peso
        if not self.dirigido:
            self._adyacencia[destino][origen] = peso

    def contiene(self, nodo: str) -> bool:
        return nodo in self._adyacencia

    def nodos(self) -> List[str]:
        return sorted(self._adyacencia)

    def vecinos(self, nodo: str) -> List[Tuple[str, float]]:
        return sorted(self._adyacencia.get(nodo, {}).items())

    def peso(self, origen: str, destino: str) -> float:
        try:
            return self._adyacencia[origen][destino]
        except KeyError:
            raise ErrorRuta(f"no existe la arista {origen} -> {destino}") from None

    def aristas(self) -> List[Tuple[str, str, float]]:
        resultado = []
        for origen in self.nodos():
            for destino, peso in self.vecinos(origen):
                if self.dirigido or origen < destino:
                    resultado.append((origen, destino, peso))
        return resultado

    def grado(self, nodo: str) -> int:
        return len(self._adyacencia.get(nodo, {}))

    def __len__(self) -> int:
        return len(self._adyacencia)


def bfs(grafo: Grafo, origen: str) -> List[str]:
    if not grafo.contiene(origen):
        raise ErrorRuta(f"nodo inexistente: {origen}")
    visitados = {origen}
    orden = []
    cola = deque([origen])
    while cola:
        actual = cola.popleft()
        orden.append(actual)
        for vecino, _ in grafo.vecinos(actual):
            if vecino not in visitados:
                visitados.add(vecino)
                cola.append(vecino)
    return orden


def dfs(grafo: Grafo, origen: str) -> List[str]:
    if not grafo.contiene(origen):
        raise ErrorRuta(f"nodo inexistente: {origen}")
    visitados = set()
    orden = []
    pila = [origen]
    while pila:
        actual = pila.pop()
        if actual in visitados:
            continue
        visitados.add(actual)
        orden.append(actual)
        for vecino, _ in reversed(grafo.vecinos(actual)):
            if vecino not in visitados:
                pila.append(vecino)
    return orden


def camino_menos_saltos(grafo: Grafo, origen: str, destino: str) -> List[str]:
    padres: Dict[str, Optional[str]] = {origen: None}
    cola = deque([origen])
    while cola:
        actual = cola.popleft()
        if actual == destino:
            break
        for vecino, _ in grafo.vecinos(actual):
            if vecino not in padres:
                padres[vecino] = actual
                cola.append(vecino)
    if destino not in padres:
        raise ErrorRuta(f"no hay camino de {origen} a {destino}")
    camino = []
    nodo: Optional[str] = destino
    while nodo is not None:
        camino.append(nodo)
        nodo = padres[nodo]
    return camino[::-1]


def dijkstra(grafo: Grafo, origen: str) -> Tuple[Dict[str, float], Dict[str, Optional[str]]]:
    """Distancias mínimas desde ``origen`` a todos los nodos (pesos no negativos)."""
    if not grafo.contiene(origen):
        raise ErrorRuta(f"nodo inexistente: {origen}")
    distancias = {nodo: math.inf for nodo in grafo.nodos()}
    previos: Dict[str, Optional[str]] = {nodo: None for nodo in grafo.nodos()}
    distancias[origen] = 0.0
    cola: List[Tuple[float, str]] = [(0.0, origen)]
    visitados = set()
    while cola:
        distancia_actual, actual = heapq.heappop(cola)
        if actual in visitados:
            continue
        visitados.add(actual)
        for vecino, peso in grafo.vecinos(actual):
            if vecino in visitados:
                continue
            nueva = distancia_actual + peso
            if peso < distancias[vecino]:
                distancias[vecino] = nueva
                previos[vecino] = actual
                heapq.heappush(cola, (nueva, vecino))
    return distancias, previos


def reconstruir_ruta(previos: Dict[str, Optional[str]], destino: str) -> List[str]:
    ruta = []
    nodo: Optional[str] = destino
    while nodo is not None:
        ruta.append(nodo)
        nodo = previos[nodo]
    return ruta[::-1]


def ruta_mas_corta(grafo: Grafo, origen: str, destino: str) -> Tuple[float, List[str]]:
    distancias, previos = dijkstra(grafo, origen)
    if destino not in distancias:
        raise ErrorRuta(f"nodo inexistente: {destino}")
    if math.isinf(distancias[destino]):
        raise ErrorRuta(f"no hay ruta de {origen} a {destino}")
    return distancias[destino], reconstruir_ruta(previos, destino)


def arbol_expansion_minima(grafo: Grafo) -> Tuple[List[Tuple[str, str, float]], float]:
    """Algoritmo de Kruskal; regresa (aristas del árbol, peso total)."""
    if grafo.dirigido:
        raise ErrorRuta("Kruskal requiere un grafo no dirigido")
    conjuntos = UnionFind(grafo.nodos())
    arbol = []
    total = 0.0
    for origen, destino, peso in sorted(grafo.aristas(), key=lambda a: (a[2], a[0], a[1])):
        if conjuntos.unir(origen, destino):
            arbol.append((origen, destino, peso))
            total += peso
    return arbol, total


def componentes_conexas(grafo: Grafo) -> List[List[str]]:
    conjuntos = UnionFind(grafo.nodos())
    for origen, destino, _ in grafo.aristas():
        conjuntos.unir(origen, destino)
    return conjuntos.grupos()


def orden_topologico(dependencias: Dict[str, Sequence[str]]) -> List[str]:
    """Orden de ejecución de tareas. ``dependencias`` mapea tarea -> prerrequisitos."""
    tareas = set(dependencias)
    for prerrequisitos in dependencias.values():
        tareas.update(prerrequisitos)
    grado_entrada = {t: 0 for t in tareas}
    sucesores: Dict[str, List[str]] = defaultdict(list)
    for tarea, prerrequisitos in dependencias.items():
        for previo in prerrequisitos:
            sucesores[previo].append(tarea)
            grado_entrada[tarea] += 1
    listas = [t for t, g in grado_entrada.items() if g == 0]
    heapq.heapify(listas)
    orden = []
    while listas:
        actual = heapq.heappop(listas)
        orden.append(actual)
        for siguiente in sucesores[actual]:
            grado_entrada[siguiente] -= 1
            if grado_entrada[siguiente] == 0:
                heapq.heappush(listas, siguiente)
    if len(orden) != len(tareas):
        raise ErrorRuta("las dependencias contienen un ciclo")
    return orden


def plan_reparto_vecino_mas_cercano(grafo: Grafo, origen: str, destinos: Iterable[str]) -> Tuple[List[str], float]:
    """Heurística del vecino más cercano para ordenar las paradas de un camión."""
    pendientes = set(destinos)
    for destino in pendientes:
        if not grafo.contiene(destino):
            raise ErrorRuta(f"destino inexistente: {destino}")
    actual = origen
    orden: List[str] = []
    total = 0.0
    while pendientes:
        distancias, _ = dijkstra(grafo, actual)
        siguiente = min(pendientes, key=lambda d: (distancias[d], d))
        if math.isinf(distancias[siguiente]):
            raise ErrorRuta(f"no hay ruta de {actual} a {siguiente}")
        total += distancias[siguiente]
        orden.append(siguiente)
        pendientes.remove(siguiente)
        actual = siguiente
    return orden, total


def red_reparto_demo() -> Grafo:
    """Red simplificada de la zona metropolitana de Guadalajara (km aproximados)."""
    grafo = Grafo()
    tramos = (
        ("CEDIS", "Zapopan", 12), ("CEDIS", "Guadalajara Centro", 9), ("CEDIS", "Tlaquepaque", 7),
        ("Guadalajara Centro", "Zapopan", 8), ("Guadalajara Centro", "Tlaquepaque", 6),
        ("Tlaquepaque", "Tonalá", 7), ("Guadalajara Centro", "Tonalá", 15),
        ("Tlaquepaque", "Tlajomulco", 18), ("CEDIS", "Tlajomulco", 22),
        ("Tlaquepaque", "El Salto", 14), ("El Salto", "Chapala", 30),
        ("Tlajomulco", "Chapala", 35), ("Tonalá", "El Salto", 16),
    )
    for origen, destino, km in tramos:
        grafo.agregar_arista(origen, destino, float(km))
    return grafo


# ==============================================================================
# SECCIÓN 21. EVALUADOR DE FÓRMULAS (listas de precios configurables)
# ==============================================================================


@dataclass(frozen=True)
class Token:
    tipo: str   # "num" | "nombre" | "op"
    valor: Any


_PATRON_TOKEN = re.compile(r"\s*(?:(\d+\.\d*|\.\d+|\d+)|([A-Za-z_][A-Za-z_0-9]*)|(\*\*|[+\-*/%^(),]))")

_OPERADORES: Dict[str, Tuple[int, str]] = {
    "+": (1, "izq"),
    "-": (1, "izq"),
    "*": (2, "izq"),
    "/": (2, "izq"),
    "%": (2, "izq"),
    "neg": (3, "der"),
    "^": (4, "der"),
}

FUNCIONES_FORMULA: Dict[str, Tuple[Callable[..., float], Optional[int]]] = {
    "min": (lambda *a: min(a), None),
    "max": (lambda *a: max(a), None),
    "abs": (abs, 1),
    "raiz": (math.sqrt, 1),
    "redondear": (lambda x, n=0: round(x, int(n)), None),
    "piso": (math.floor, 1),
    "techo": (math.ceil, 1),
}

_INICIO_OPERANDO = (None, "op", "abre", "coma")


def tokenizar(expresion: str) -> List[Token]:
    tokens: List[Token] = []
    expresion = expresion.strip()
    posicion = 0
    while posicion < len(expresion):
        coincidencia = _PATRON_TOKEN.match(expresion, posicion)
        if not coincidencia or coincidencia.end() == posicion:
            raise ErrorParser(f"carácter inesperado en la posición {posicion}: {expresion[posicion]!r}")
        numero, nombre, simbolo = coincidencia.groups()
        if numero is not None:
            tokens.append(Token("num", float(numero)))
        elif nombre is not None:
            tokens.append(Token("nombre", nombre))
        else:
            tokens.append(Token("op", simbolo))
        posicion = coincidencia.end()
    return tokens


def a_notacion_polaca_inversa(tokens: Sequence[Token]) -> List[Tuple[Any, ...]]:
    """Algoritmo shunting-yard con soporte de funciones, comas y menos unario."""
    salida: List[Tuple[Any, ...]] = []
    pila: List[Tuple[str, Any]] = []
    comas: List[int] = []
    previo: Optional[str] = None
    for indice, token in enumerate(tokens):
        if token.tipo == "num":
            if previo == "operando":
                raise ErrorParser("falta un operador entre dos operandos")
            salida.append(("num", token.valor))
            previo = "operando"
        elif token.tipo == "nombre":
            if previo == "operando":
                raise ErrorParser("falta un operador entre dos operandos")
            siguiente = tokens[indice + 1] if indice + 1 < len(tokens) else None
            if siguiente is not None and siguiente.tipo == "op" and siguiente.valor == "(":
                if token.valor not in FUNCIONES_FORMULA:
                    raise ErrorParser(f"función desconocida: {token.valor}")
                pila.append(("func", token.valor))
                previo = "func"
            else:
                salida.append(("var", token.valor))
                previo = "operando"
        elif token.valor == "(":
            if previo == "operando":
                raise ErrorParser("no se admite multiplicación implícita")
            es_funcion = previo == "func"
            pila.append(("par", es_funcion))
            if es_funcion:
                comas.append(0)
            previo = "abre"
        elif token.valor == ",":
            while pila and pila[-1][0] != "par":
                salida.append(pila.pop())
            if not pila or not pila[-1][1]:
                raise ErrorParser("coma fuera de una llamada a función")
            if previo in _INICIO_OPERANDO:
                raise ErrorParser("argumento vacío")
            comas[-1] += 1
            previo = "coma"
        elif token.valor == ")":
            while pila and pila[-1][0] != "par":
                salida.append(pila.pop())
            if not pila:
                raise ErrorParser("paréntesis de cierre sin apertura")
            _, es_funcion = pila.pop()
            if es_funcion:
                numero_comas = comas.pop()
                if previo == "coma":
                    raise ErrorParser("argumento vacío")
                argumentos = 0 if previo == "abre" else numero_comas + 1
                _, nombre = pila.pop()
                salida.append(("func", nombre, argumentos))
            elif previo == "abre":
                raise ErrorParser("paréntesis vacíos")
            elif previo in _INICIO_OPERANDO:
                raise ErrorParser("expresión incompleta antes de ')'")
            previo = "operando"
        else:
            simbolo = "^" if token.valor == "**" else token.valor
            if previo in _INICIO_OPERANDO:
                if simbolo == "-":
                    pila.append(("op", "neg"))
                    previo = "op"
                    continue
                if simbolo == "+":
                    continue
                raise ErrorParser(f"operador '{simbolo}' mal colocado")
            precedencia, asociatividad = _OPERADORES[simbolo]
            while pila and pila[-1][0] == "op":
                precedencia_tope = _OPERADORES[pila[-1][1]][0]
                if precedencia_tope > precedencia or (precedencia_tope == precedencia and asociatividad == "izq"):
                    salida.append(pila.pop())
                else:
                    break
            pila.append(("op", simbolo))
            previo = "op"
    if previo in _INICIO_OPERANDO or previo == "func":
        raise ErrorParser("expresión vacía o incompleta")
    while pila:
        elemento = pila.pop()
        if elemento[0] == "par":
            raise ErrorParser("paréntesis sin cerrar")
        salida.append(elemento)
    return salida


def evaluar_rpn(rpn: Sequence[Tuple[Any, ...]], variables: Optional[Dict[str, float]] = None) -> float:
    variables = variables or {}
    pila: List[float] = []
    for elemento in rpn:
        tipo = elemento[0]
        if tipo == "num":
            pila.append(elemento[1])
        elif tipo == "var":
            nombre = elemento[1]
            if nombre not in variables:
                raise ErrorParser(f"variable no definida: {nombre}")
            pila.append(float(variables[nombre]))
        elif tipo == "op":
            operador = elemento[1]
            if operador == "neg":
                if not pila:
                    raise ErrorParser("faltan operandos")
                pila.append(-pila.pop())
                continue
            if len(pila) < 2:
                raise ErrorParser("faltan operandos")
            b = pila.pop()
            a = pila.pop()
            if operador == "+":
                resultado = a + b
            elif operador == "-":
                resultado = a - b
            elif operador == "*":
                resultado = a * b
            elif operador in ("/", "%"):
                if b == 0:
                    raise ErrorParser("división entre cero")
                resultado = a / b if operador == "/" else a % b
            elif operador == "^":
                resultado = a ** b
                if isinstance(resultado, complex):
                    raise ErrorParser("la potencia produjo un número complejo")
            else:
                raise ErrorParser(f"operador desconocido: {operador}")
            pila.append(resultado)
        elif tipo == "func":
            nombre, argumentos = elemento[1], elemento[2]
            funcion, aridad = FUNCIONES_FORMULA[nombre]
            if aridad is not None and argumentos != aridad:
                raise ErrorParser(f"{nombre}() espera {aridad} argumento(s), recibió {argumentos}")
            if argumentos == 0 or len(pila) < argumentos:
                raise ErrorParser(f"{nombre}() requiere argumentos")
            valores = pila[-argumentos:]
            del pila[-argumentos:]
            try:
                pila.append(float(funcion(*valores)))
            except (TypeError, ValueError) as exc:
                raise ErrorParser(f"error al evaluar {nombre}(): {exc}") from None
        else:
            raise ErrorParser(f"elemento desconocido: {elemento!r}")
    if len(pila) != 1:
        raise ErrorParser("expresión mal formada")
    return pila[0]


def evaluar_expresion(expresion: str, variables: Optional[Dict[str, float]] = None) -> float:
    return evaluar_rpn(a_notacion_polaca_inversa(tokenizar(expresion)), variables)


def variables_de_expresion(expresion: str) -> List[str]:
    rpn = a_notacion_polaca_inversa(tokenizar(expresion))
    return sorted({e[1] for e in rpn if e[0] == "var"})


FORMULA_PRECIO_DEFAULT = "redondear(costo * (1 + margen / 100) * (1 + iva), 2)"


def calcular_precio_por_formula(costo: float, margen: float = 30.0, formula: str = FORMULA_PRECIO_DEFAULT,
                                **extras: float) -> float:
    variables = {"costo": costo, "margen": margen, "iva": TASA_IVA}
    variables.update(extras)
    return evaluar_expresion(formula, variables)


# ==============================================================================
# SECCIÓN 22. ANALÍTICA DE VENTAS
# ==============================================================================


def resumen_estadistico(valores: Iterable[float]) -> Dict[str, Any]:
    valores = list(valores)
    if not valores:
        return {"n": 0}
    return {
        "n": len(valores),
        "suma": round(sum(valores), 2),
        "promedio": round(promedio(valores), 2),
        "mediana": round(mediana(valores), 2),
        "minimo": min(valores),
        "maximo": max(valores),
        "desviacion": round(desviacion_estandar(valores), 2) if len(valores) > 1 else 0.0,
        "p90": round(percentil(valores, 90), 2),
    }


def ventas_por_dia(ventas: Iterable[Dict[str, Any]]) -> Dict[str, float]:
    totales: Dict[str, float] = defaultdict(float)
    for venta in ventas:
        totales[venta["fecha"]] += venta["total"]
    return {fecha: round(total, 2) for fecha, total in sorted(totales.items())}


def unidades_por_producto(ventas: Iterable[Dict[str, Any]]) -> Counter:
    conteo: Counter = Counter()
    for venta in ventas:
        for linea in venta["lineas"]:
            conteo[linea["sku"]] += linea["cantidad"]
    return conteo


def productos_mas_vendidos(ventas: Iterable[Dict[str, Any]], n: int = 5) -> List[Tuple[str, int]]:
    conteo = unidades_por_producto(ventas)
    return sorted(conteo.items(), key=lambda par: (-par[1], par[0]))[:n]


def ticket_promedio(ventas: Sequence[Dict[str, Any]]) -> float:
    if not ventas:
        return 0.0
    return round(promedio(v["total"] for v in ventas), 2)


def analisis_abc(importes_por_producto: Dict[str, float], corte_a: float = 0.80, corte_b: float = 0.95) -> Dict[str, str]:
    """Clasificación ABC (Pareto) por participación acumulada en el importe vendido."""
    total = sum(importes_por_producto.values())
    if total <= 0:
        return {sku: "C" for sku in importes_por_producto}
    clasificacion = {}
    acumulado_previo = 0.0
    for sku, importe in sorted(importes_por_producto.items(), key=lambda p: (-p[1], p[0])):
        if acumulado_previo < corte_a * total:
            clasificacion[sku] = "A"
        elif acumulado_previo < corte_b * total:
            clasificacion[sku] = "B"
        else:
            clasificacion[sku] = "C"
        acumulado_previo += importe
    return clasificacion


def pronostico_promedio_movil(serie: Sequence[float], ventana: int = 3, periodos: int = 1) -> List[float]:
    if len(serie) < ventana:
        raise ValueError("la serie es más corta que la ventana")
    historico = list(serie)
    pronostico = []
    for _ in range(periodos):
        siguiente = round(promedio(historico[-ventana:]), 2)
        pronostico.append(siguiente)
        historico.append(siguiente)
    return pronostico


def detectar_anomalias(valores: Sequence[float], umbral: float = 2.0) -> List[int]:
    if len(valores) < 3:
        return []
    return [i for i, z in enumerate(puntaje_z(valores)) if abs(z) > umbral]


# ==============================================================================
# SECCIÓN 23. CARGA DE CATÁLOGOS Y SIMULACIÓN
# ==============================================================================


def cargar_catalogos_demo(registros_por_catalogo: int = 10) -> Dict[str, RepositorioMemoria]:
    catalogos: Dict[str, RepositorioMemoria] = {}
    for nombre, (_, clase_repositorio, generador) in CATALOGO_ENTIDADES.items():
        repositorio = clase_repositorio()
        repositorio.agregar_varios(generador(registros_por_catalogo))
        catalogos[nombre] = repositorio
    return catalogos


def construir_inventario_demo(semilla: int = 2024) -> Inventario:
    rng = random.Random(semilla)
    inventario = Inventario()
    categorias = ("abarrotes", "lacteos", "bebidas", "limpieza", "higiene")
    for indice, nombre in enumerate(PRODUCTOS_DEMO, start=1):
        sku = f"ABA-{indice:05d}"
        costo = round(rng.uniform(8, 90), 2)
        precio = round(costo * rng.uniform(1.18, 1.45), 2)
        inventario.dar_de_alta(
            sku, f"{nombre} {rng.choice(PRESENTACIONES_DEMO)}", precio, costo,
            minimo=rng.randint(5, 20), categoria=rng.choice(categorias),
        )
        inventario.registrar_entrada(sku, rng.randint(15, 60), costo, fecha=date(2026, 1, 2), referencia="INV-INICIAL")
    return inventario


def simular_jornada(semilla: int = 42, num_ventas: int = 30, fecha: date = date(2026, 3, 14)) -> Dict[str, Any]:
    rng = random.Random(semilla)
    inventario = construir_inventario_demo(semilla)
    folios = GeneradorFolios("V")
    ventas: List[Dict[str, Any]] = []
    rechazadas = 0
    skus = inventario.skus_ordenados()
    for _ in range(num_ventas):
        carrito = Carrito(inventario, cliente_id=rng.randint(1, 500))
        for _ in range(rng.randint(1, 6)):
            carrito.agregar(rng.choice(skus), rng.randint(1, 6), descuento_pct=rng.choice((0, 0, 0, 5, 10)))
        try:
            venta = procesar_venta(
                carrito, folios, fecha=fecha,
                forma_pago=rng.choice(("efectivo", "tarjeta_debito", "tarjeta_credito")),
            )
        except StockInsuficiente:
            rechazadas += 1
            carrito.vaciar()
            continue
        ventas.append(venta)
    totales = [v["total"] for v in ventas]
    return {
        "ventas": ventas,
        "rechazadas": rechazadas,
        "inventario": inventario,
        "estadisticas": resumen_estadistico(totales),
        "top_productos": productos_mas_vendidos(ventas, 5),
        "valor_inventario": inventario.valor_inventario(),
    }


def imprimir_demo() -> None:
    print(encabezado_reporte("SIMULACIÓN DE UNA JORNADA DE VENTAS"))
    resultado = simular_jornada()
    ventas = resultado["ventas"]
    print(f"Ventas procesadas: {len(ventas)}   Rechazadas por falta de stock: {resultado['rechazadas']}")
    print()
    print(tabla_texto(
        ["Estadística", "Valor"],
        [[k, v] for k, v in resultado["estadisticas"].items()],
    ))
    print()
    print("Productos más vendidos:")
    print(histograma_texto(dict(resultado["top_productos"])))
    print()
    if ventas:
        print(generar_ticket(ventas[0]))
        print()
    print(f"Valor del inventario al cierre: {formatear_moneda(resultado['valor_inventario'])}")
    print()
    distancia, ruta = ruta_mas_corta(red_reparto_demo(), "CEDIS", "Chapala")
    print(f"Ruta CEDIS -> Chapala: {' -> '.join(ruta)} ({distancia:.0f} km)")
    print()
    catalogos = cargar_catalogos_demo(8)
    print(tabla_texto(["Catálogo", "Registros"], [[n, len(r)] for n, r in catalogos.items()]))
    print()
    print(reporte_productos(catalogos["productos"]))


# ==============================================================================
# SECCIÓN 24. PRUEBAS INTERNAS
# ==============================================================================
#
# Cada función cuyo nombre empieza con ``test_`` se ejecuta automáticamente con
# ``python sistema_tienda.py``. Las pruebas no requieren pytest.


def _igual(obtenido: Any, esperado: Any, contexto: str = "") -> None:
    if obtenido != esperado:
        prefijo = f"{contexto}: " if contexto else ""
        raise AssertionError(f"{prefijo}se esperaba {esperado!r}, se obtuvo {obtenido!r}")


def _cerca(obtenido: float, esperado: float, tolerancia: float = 1e-6, contexto: str = "") -> None:
    if abs(obtenido - esperado) > tolerancia:
        prefijo = f"{contexto}: " if contexto else ""
        raise AssertionError(f"{prefijo}se esperaba {esperado!r} (±{tolerancia}), se obtuvo {obtenido!r}")


def _lanza(tipo_excepcion: type, funcion: Callable, *args: Any, **kwargs: Any) -> BaseException:
    try:
        funcion(*args, **kwargs)
    except tipo_excepcion as exc:
        return exc
    raise AssertionError(f"se esperaba {tipo_excepcion.__name__} al llamar {getattr(funcion, '__name__', funcion)}")


# --- texto -------------------------------------------------------------------

def test_quitar_acentos_y_slugify():
    _igual(quitar_acentos("Ñandú café"), "Nandu cafe")
    _igual(slugify("¡Oferta de Año Nuevo 2026!"), "oferta-de-ano-nuevo-2026")
    _igual(slugify("  --Leche   Entera 1 L--  "), "leche-entera-1-l")


def test_capitalizar_y_truncar():
    _igual(capitalizar_nombre("  maría DE la  luz   GARCÍA "), "María de la Luz García")
    _igual(truncar("Abarrotes del Bajío", 10), "Abarrot...")
    _igual(truncar("corto", 10), "corto")
    _igual(truncar("abcdef", 2), "..")
    _igual(enmascarar("4111111111111111"), "************1111")


def test_utilerias_de_texto_varias():
    _igual(contar_palabras("Leche, leche y más LECHE")["leche"], 3)
    _igual(extraer_numeros("Total: 1,234.50 y 7 piezas, -3 de ajuste"), [1234.5, 7.0, -3.0])
    assert es_palindromo("Anita lava la tina")
    assert not es_palindromo("Abarrotes")
    _igual(rellenar_plantilla("Hola {{ nombre }}, tu saldo es {{saldo}}", nombre="Ana", saldo=10), "Hola Ana, tu saldo es 10")
    _lanza(KeyError, rellenar_plantilla, "{{falta}}")


def test_validaciones_de_contacto():
    assert es_email_valido("compras@abarrotesbajio.mx")
    assert not es_email_valido("compras@@abarrotes")
    assert es_telefono_valido("(33) 3615-1234")
    assert es_telefono_valido("+52 33 3615 1234")
    assert not es_telefono_valido("3615-1234")
    assert es_rfc_valido("ABA950315KT2")
    assert es_rfc_valido("GOMA850101H12")
    assert not es_rfc_valido("ABA951315KT2")
    _igual(tipo_persona_por_rfc("ABA950315KT2"), "persona_moral")
    _igual(tipo_persona_por_rfc("GOMA850101H12"), "persona_fisica")


def test_monto_a_letras():
    _igual(monto_a_letras(1234.56), "MIL DOSCIENTOS TREINTA Y CUATRO PESOS 56/100 M.N.")
    _igual(monto_a_letras(1), "UN PESO 00/100 M.N.")
    _igual(monto_a_letras(21), "VEINTIÚN PESOS 00/100 M.N.")
    _igual(monto_a_letras(100), "CIEN PESOS 00/100 M.N.")
    _igual(monto_a_letras(1_000_000), "UN MILLÓN DE PESOS 00/100 M.N.")
    _igual(monto_a_letras(2_501_100.10), "DOS MILLONES QUINIENTOS UN MIL CIEN PESOS 10/100 M.N.")


def test_levenshtein_y_similitud():
    _igual(levenshtein("gato", "pato"), 1)
    _igual(levenshtein("kitten", "sitting"), 3)
    _igual(levenshtein("", "abc"), 3)
    _cerca(similitud("Azúcar", "azucar"), 1.0)
    _igual(sugerir_coincidencias("lechee", ["leche", "lechuga", "café"]), ["leche"])


def test_ean13_y_luhn():
    _igual(digito_verificador_ean13("400638133393"), 1)
    assert validar_ean13("4006381333931")
    assert not validar_ean13("4006381333932")
    assert validar_luhn("79927398713")
    assert not validar_luhn("79927398710")


# --- fechas ------------------------------------------------------------------

def test_es_bisiesto():
    assert es_bisiesto(2024)
    assert not es_bisiesto(2023)
    assert not es_bisiesto(1900), "1900 es centenario no divisible entre 400"
    assert es_bisiesto(2000), "2000 es divisible entre 400 y por lo tanto bisiesto"


def test_dias_en_mes():
    _igual(dias_en_mes(2026, 1), 31)
    _igual(dias_en_mes(2026, 4), 30)
    _igual(dias_en_mes(2024, 2), 29)
    _igual(dias_en_mes(1900, 2), 28)
    _igual(dias_en_mes(2000, 2), 29, "febrero del 2000")
    _igual(dias_en_anio(2000), 366, "días del año 2000")
    _lanza(ValueError, dias_en_mes, 2026, 13)


def test_sumar_meses():
    _igual(sumar_meses(date(2024, 1, 31), 1), date(2024, 2, 29))
    _igual(sumar_meses(date(2025, 12, 15), 3), date(2026, 3, 15))
    _igual(sumar_meses(date(2024, 3, 31), -1), date(2024, 2, 29))
    _igual(sumar_meses(date(2024, 1, 15), -2), date(2023, 11, 15))
    _igual(fin_de_mes(date(2026, 11, 18)), date(2026, 11, 30))


def test_dias_habiles():
    assert date(2026, 11, 16) in festivos_del_anio(2026), "tercer lunes de noviembre"
    _igual(sumar_dias_habiles(date(2026, 11, 13), 1), date(2026, 11, 17))
    _igual(sumar_dias_habiles(date(2026, 11, 17), -1), date(2026, 11, 13))
    _igual(dias_habiles_entre(date(2026, 11, 13), date(2026, 11, 20)), 4)
    _igual(dias_habiles_entre(date(2026, 11, 20), date(2026, 11, 13)), -4)


def test_parsear_fecha_y_edad():
    _igual(parsear_fecha("14/03/2026"), date(2026, 3, 14))
    _igual(parsear_fecha("2026-03-14"), date(2026, 3, 14))
    _igual(parsear_fecha("20260314"), date(2026, 3, 14))
    _lanza(ValueError, parsear_fecha, "marzo 14")
    _igual(edad(date(1990, 11, 19), date(2026, 11, 18)), 35)
    _igual(edad(date(1990, 11, 18), date(2026, 11, 18)), 36)
    _igual(trimestre(date(2026, 11, 18)), 4)
    _igual(fecha_larga(date(2026, 3, 14)), "sábado 14 de marzo de 2026")


# --- números y estadística ---------------------------------------------------

def test_redondeos():
    _igual(redondear_bancario(2.345), 2.34)
    _igual(redondear_bancario(2.355), 2.36)
    _igual(redondear_moneda(2.345), 2.35)
    _igual(redondear_a_multiplo(17.3, 0.5), 17.5)
    _igual(limitar(15, 0, 10), 10)


def test_promedio():
    _igual(promedio([2, 4, 6]), 4)
    _igual(promedio([1, 2]), 1.5)
    _cerca(promedio([2.5, 3.5, 4.0]), 10 / 3)
    _lanza(ValueError, promedio, [])


def test_mediana_moda_percentil():
    _igual(mediana([5, 1, 3]), 3.0)
    _igual(mediana([4, 1, 3, 2]), 2.5)
    _igual(moda([3, 1, 3, 1, 2]), 1)
    _igual(percentil([1, 2, 3, 4, 5], 50), 3.0)
    _cerca(percentil([10, 20, 30, 40], 90), 37.0)
    _cerca(promedio_ponderado([10, 20], [1, 3]), 17.5)


def test_varianza_y_desviacion():
    datos = [2, 4, 4, 4, 5, 5, 7, 9]
    _cerca(varianza(datos, muestral=False), 4.0)
    _cerca(desviacion_estandar(datos, muestral=False), 2.0)
    _cerca(varianza(datos), 32 / 7)


def test_regresion_y_correlacion():
    x = [1, 2, 3, 4, 5]
    y = [3, 5, 7, 9, 11]
    pendiente, intercepto = regresion_lineal_simple(x, y)
    _cerca(pendiente, 2.0)
    _cerca(intercepto, 1.0)
    _cerca(correlacion_pearson(x, y), 1.0)
    _igual(media_movil([1, 2, 3, 4, 5], 3), [2.0, 3.0, 4.0])
    _igual(normalizar_min_max([10, 20, 30]), [0.0, 0.5, 1.0])


def test_finanzas():
    _cerca(interes_compuesto(1000, 0.12, 1), 1126.825, 0.001)
    _cerca(pago_mensual(10_000, 0.12, 12), 888.49, 0.005)
    tabla = tabla_amortizacion(10_000, 0.12, 12)
    _igual(len(tabla), 12)
    _igual(tabla[-1]["saldo"], 0.0)
    _cerca(sum(f["abono_capital"] for f in tabla), 10_000, 0.05)
    _cerca(tasa_interna_retorno([-1000, 1100]), 0.10, 1e-6)
    _cerca(valor_presente_neto(0.10, [-1000, 1100]), 0.0, 1e-6)
    _igual(depreciacion_linea_recta(10_000, 1_000, 3), [7000.0, 4000.0, 1000.0])


# --- estructuras de datos ----------------------------------------------------

def test_lru_cache():
    cache = LRUCache(2)
    cache.guardar("a", 1)
    cache.guardar("b", 2)
    _igual(cache.obtener("a"), 1)
    cache.guardar("c", 3)
    assert "a" in cache, "'a' se usó recientemente y no debía ser desalojada"
    assert "b" not in cache, "'b' era la menos recientemente usada"
    _igual(cache.claves(), ["a", "c"])
    _igual(cache.obtener("zzz", "nada"), "nada")
    _cerca(cache.tasa_aciertos(), 0.5)


def test_memoizar():
    llamadas = []

    @memoizar(capacidad=2)
    def cuadrado(x):
        llamadas.append(x)
        return x * x

    for valor in (2, 3, 2, 4, 2):
        cuadrado(valor)
    _igual(llamadas, [2, 3, 4], "llamadas reales a la función memoizada")
    _igual(cuadrado.cache.aciertos, 2)


def test_pila_cola_y_prioridad():
    pila = Pila([1, 2])
    pila.apilar(3)
    _igual(pila.desapilar(), 3)
    _igual(pila.cima(), 2)
    cola = Cola()
    cola.encolar("x")
    cola.encolar("y")
    _igual(cola.desencolar(), "x")
    prioridad = ColaPrioridad()
    prioridad.agregar("normal", 5)
    prioridad.agregar("urgente", 1)
    prioridad.agregar("normal-2", 5)
    _igual([prioridad.extraer() for _ in range(3)], ["urgente", "normal", "normal-2"])
    _lanza(IndexError, prioridad.extraer)


def test_trie():
    trie = Trie(["leche", "lechuga", "lenteja", "arroz"])
    _igual(trie.con_prefijo("lec"), ["leche", "lechuga"])
    assert trie.contiene("arroz")
    assert not trie.contiene("arr")
    assert trie.eliminar("leche")
    _igual(trie.con_prefijo("le"), ["lechuga", "lenteja"])
    _igual(len(trie), 3)


def test_union_find():
    conjuntos = UnionFind("abcde")
    conjuntos.unir("a", "b")
    conjuntos.unir("c", "d")
    conjuntos.unir("b", "d")
    assert conjuntos.conectados("a", "c")
    assert not conjuntos.conectados("a", "e")
    _igual(conjuntos.componentes, 2)
    _igual(conjuntos.grupos(), [["e"], ["a", "b", "c", "d"]])


def test_filtro_bloom():
    filtro = FiltroBloom(4096, 3)
    for i in range(100):
        filtro.agregar(f"V-{i:06d}")
    assert all(filtro.posiblemente_contiene(f"V-{i:06d}") for i in range(100))
    assert filtro.tasa_falsos_positivos_estimada() < 0.01


def test_busqueda_binaria():
    datos = [1, 3, 5, 7, 9, 11]
    for indice, valor in enumerate(datos):
        _igual(busqueda_binaria(datos, valor), indice, f"posición de {valor}")
    _igual(busqueda_binaria(datos, 4), -1)
    _igual(busqueda_binaria([42], 42), 0, "lista de un elemento")
    _igual(busqueda_binaria([], 1), -1)


def test_ordenamientos():
    datos = [5, 3, 9, 1, 3, 8, 0]
    esperado = sorted(datos)
    _igual(merge_sort(datos), esperado)
    _igual(quick_sort(datos), esperado)
    _igual(insertion_sort(datos), esperado)
    _igual(heap_sort(datos), esperado)
    _igual(top_k(datos, 2), [9, 8])
    estable = merge_sort([("b", 1), ("a", 1), ("c", 0)], clave=lambda t: t[1])
    _igual(estable, [("c", 0), ("b", 1), ("a", 1)])
    lista = [1, 3, 5]
    _igual(insertar_ordenado(lista, 4), 2)
    _igual(lista, [1, 3, 4, 5])


def test_utilerias_de_colecciones():
    pagina = paginar(list(range(23)), 3, 10)
    _igual(pagina["elementos"], [20, 21, 22])
    _igual(pagina["total_paginas"], 3)
    assert not pagina["tiene_siguiente"]
    _igual(agrupar_por([1, 2, 3, 4], lambda x: x % 2), {1: [1, 3], 0: [2, 4]})
    _igual(contar_por("abracadabra", lambda c: c)["a"], 5)
    _igual(aplanar([1, [2, [3, (4, 5)]], 6]), [1, 2, 3, 4, 5, 6])
    _igual(dividir_en_bloques([1, 2, 3, 4, 5], 2), [[1, 2], [3, 4], [5]])
    _igual(unicos_preservando_orden([3, 1, 3, 2, 1]), [3, 1, 2])
    _igual(list(ventana_deslizante([1, 2, 3, 4], 3)), [(1, 2, 3), (2, 3, 4)])
    _lanza(ValueError, indexar_por, [1, 1], lambda x: x)


def test_tabla_texto_e_histograma():
    tabla = tabla_texto(["Producto", "Precio"], [["Leche", 25.5], ["Pan", 4.0]])
    lineas = tabla.splitlines()
    _igual(len(lineas), 4)
    assert lineas[2].endswith("25.50"), "las columnas numéricas se alinean a la derecha"
    assert "##########" in histograma_texto({"a": 10, "b": 5}, ancho=10)


def test_configuracion():
    config = Configuracion({"ticket": {"ancho": 48}})
    _igual(config.obtener("ticket.ancho"), 48)
    _igual(config.obtener("ticket.leyenda"), "GRACIAS POR SU COMPRA")
    _igual(config.obtener("no.existe", "x"), "x")
    config.establecer("impresora.puerto", "USB001")
    _igual(config.obtener("impresora.puerto"), "USB001")
    _igual(CONFIGURACION_POR_DEFECTO["ticket"]["ancho"], 42, "la configuración por defecto no debe mutar")
    _igual(config.validar(), [])
    config.establecer("ticket.ancho", 10)
    _igual(len(config.validar()), 1)


# --- inventario --------------------------------------------------------------

def _inventario_basico() -> Inventario:
    inventario = Inventario()
    inventario.dar_de_alta("ABA-00001", "Frijol bayo 1 kg", 38.50, 10.0, minimo=20, categoria="abarrotes")
    inventario.dar_de_alta("ABA-00002", "Leche entera 1 L", 27.90, 19.0, minimo=5, categoria="lacteos")
    inventario.dar_de_alta("ABA-00003", "Refresco de cola 2 L", 42.00, 28.5, minimo=5, categoria="bebidas")
    inventario.registrar_entrada("ABA-00001", 10, 10.0, date(2026, 1, 5), "C-001")
    inventario.registrar_entrada("ABA-00001", 10, 14.0, date(2026, 1, 6), "C-002")
    inventario.registrar_entrada("ABA-00002", 30, 19.0, date(2026, 1, 6), "C-003")
    inventario.registrar_entrada("ABA-00003", 24, 28.5, date(2026, 1, 6), "C-004")
    return inventario


def test_inventario_costo_promedio():
    inventario = _inventario_basico()
    _cerca(inventario.costo_promedio("ABA-00001"), 12.0)
    inventario.registrar_salida("ABA-00001", 5, date(2026, 1, 7), "V-000001")
    _igual(inventario.existencia("ABA-00001"), 15)
    _cerca(inventario.valor_inventario(), 15 * 12.0 + 30 * 19.0 + 24 * 28.5, 0.01)
    _igual(inventario.productos_bajo_minimo(), ["ABA-00001"])
    _igual(inventario.productos_por_categoria()["lacteos"], ["ABA-00002"])


def test_inventario_validaciones():
    inventario = _inventario_basico()
    error = _lanza(StockInsuficiente, inventario.registrar_salida, "ABA-00002", 31)
    _igual(error.disponible, 30)
    _lanza(EntidadNoEncontrada, inventario.existencia, "XYZ-99999")
    _lanza(ErrorValidacion, inventario.dar_de_alta, "mal-sku", "x", 1, 1)
    _lanza(ErrorSistema, inventario.dar_de_alta, "ABA-00001", "duplicado", 1, 1)
    _igual(inventario.ajustar("ABA-00003", 20, date(2026, 1, 8)), -4)
    _igual(inventario.existencia("ABA-00003"), 20)


def test_inventario_busqueda_de_sku():
    inventario = _inventario_basico()
    for sku in ("ABA-00001", "ABA-00002", "ABA-00003"):
        assert inventario.buscar_sku(sku), f"no se encontró {sku} en el catálogo"
    assert not inventario.buscar_sku("ABA-00004")


def test_kardex():
    inventario = _inventario_basico()
    inventario.registrar_salida("ABA-00001", 4, date(2026, 1, 7), "V-000001")
    inventario.ajustar("ABA-00001", 15, date(2026, 1, 8))
    kardex = inventario.kardex("ABA-00001")
    _igual([r["saldo"] for r in kardex], [10, 20, 16, 15])
    _igual(kardex[-1]["tipo"], "ajuste")


def test_kardex_llamadas_independientes():
    movimientos_a = [MovimientoInventario(date(2026, 2, 1), "ABA-00009", "entrada", 10, 5.0, "C-100")]
    movimientos_b = [
        MovimientoInventario(date(2026, 2, 2), "ABA-00010", "entrada", 4, 7.0, "C-101"),
        MovimientoInventario(date(2026, 2, 3), "ABA-00010", "salida", 1, 7.0, "V-100"),
    ]
    kardex_a = construir_kardex(movimientos_a)
    kardex_b = construir_kardex(movimientos_b)
    _igual(len(kardex_a), 1, "renglones del primer kárdex")
    _igual(len(kardex_b), 2, "renglones del segundo kárdex")
    _igual(kardex_b[-1]["saldo"], 3)
    acumulado = construir_kardex(movimientos_a, kardex=list(kardex_b))
    _igual(len(acumulado), 3)


# --- precios -----------------------------------------------------------------

def test_aplicar_descuento():
    _igual(aplicar_descuento(200, 10), 180.0)
    _igual(aplicar_descuento(99.90, 0), 99.9)
    _igual(aplicar_descuento(50, 100), 0.0)
    _igual(aplicar_descuento(19.99, 15), 16.99)
    _lanza(ValueError, aplicar_descuento, 10, 120)


def test_precio_mayoreo_y_promociones():
    _igual(precio_mayoreo(100, 6), 100.0)
    _igual(precio_mayoreo(100, 12), 95.0)
    _igual(precio_mayoreo(100, 50), 90.0)
    _igual(precio_mayoreo(100, 500), 85.0)
    _igual(aplicar_promocion_nxm(7, 10.0), 50.0)
    _igual(margen_bruto(50, 35), 30.0)
    _igual(markup(50, 40), 25.0)


def test_iva_y_envios():
    _igual(precio_con_iva(100), 116.0)
    _igual(desglosar_iva(116), {"base": 100.0, "iva": 16.0})
    _igual(zona_por_codigo_postal("44100"), "ZMG")
    _igual(zona_por_codigo_postal("99999"), "Nacional")
    _igual(costo_envio("37000", 2.3), 140.0 + 6.5 * 3)
    _lanza(ValueError, costo_envio, "44100", 0)


# --- ventas ------------------------------------------------------------------

def test_carrito_y_subtotal():
    inventario = _inventario_basico()
    carrito = Carrito(inventario, cliente_id=7)
    carrito.agregar("ABA-00002", 2)
    carrito.agregar("ABA-00002", 1)
    carrito.agregar("ABA-00003", 1, descuento_pct=10)
    _igual(len(carrito), 2)
    _igual(carrito.total_articulos(), 4)
    _cerca(carrito.subtotal(), 27.90 * 3 + 37.80, 0.001)
    _igual(carrito.quitar("ABA-00003"), 1)


def test_procesar_venta():
    inventario = _inventario_basico()
    folios = GeneradorFolios("V", inicio=41)
    carrito = Carrito(inventario)
    carrito.agregar("ABA-00002", 2)
    carrito.agregar("ABA-00001", 1)
    venta = procesar_venta(carrito, folios, fecha=date(2026, 3, 14), pago_recibido=200)
    _igual(venta["folio"], "V-000041")
    _cerca(venta["subtotal"], 94.30, 0.001)
    _cerca(venta["iva"], 15.09, 0.001)
    _cerca(venta["total"], 109.39, 0.001)
    _cerca(venta["cambio"], 90.61, 0.001)
    _igual(inventario.existencia("ABA-00002"), 28)
    _igual(len(carrito), 0, "el carrito debe quedar vacío")
    ticket = generar_ticket(venta)
    assert "CIENTO NUEVE PESOS 39/100 M.N." in ticket
    assert "V-000041" in ticket


def test_venta_sin_existencias_no_afecta_inventario():
    inventario = _inventario_basico()
    carrito = Carrito(inventario)
    carrito.agregar("ABA-00002", 5)
    carrito.agregar("ABA-00003", 100)
    _lanza(StockInsuficiente, procesar_venta, carrito, GeneradorFolios("V"))
    _igual(inventario.existencia("ABA-00002"), 30)
    _lanza(ErrorValidacion, procesar_venta, Carrito(inventario), GeneradorFolios("V"))


def test_desglose_de_cambio():
    desglose, residuo = desglosar_cambio(387.5)
    _igual(desglose, {200: 1, 100: 1, 50: 1, 20: 1, 10: 1, 5: 1, 2: 1, 0.5: 1})
    _igual(residuo, 0.0)
    desglose, residuo = desglosar_cambio(0.30)
    _igual(desglose, {})
    _cerca(residuo, 0.30)


# --- facturación -------------------------------------------------------------

def test_impuestos_persona_fisica():
    impuestos = calcular_impuestos_factura(1000.0)
    _igual(impuestos["iva"], 160.0)
    _igual(impuestos["retencion_isr"], 0.0)
    _igual(impuestos["total"], 1160.0)
    con_ieps = calcular_impuestos_factura(1000.0, base_ieps=500.0)
    _igual(con_ieps["ieps"], 40.0)
    _igual(con_ieps["iva"], 166.4)
    _igual(con_ieps["total"], 1206.4)


def test_impuestos_persona_moral():
    impuestos = calcular_impuestos_factura(1000.0, "persona_moral")
    _igual(impuestos["iva"], 160.0)
    _igual(impuestos["retencion_isr"], 12.5)
    _igual(impuestos["retencion_iva"], 106.67)
    _igual(impuestos["total"], 1040.83)
    _lanza(ErrorValidacion, calcular_impuestos_factura, 100.0, "extranjero")


def test_factura_a_persona_moral():
    factura = Factura("A", 1520, date(2026, 11, 18), RFC_EMPRESA, "DLB010203AB4", "Distribuidora La Bodega S.A. de C.V.")
    factura.agregar_concepto(ConceptoFactura("50192100", "Botana surtida caja 24 pzas", 2, 350.0, aplica_ieps=True))
    factura.agregar_concepto(ConceptoFactura("50201700", "Café soluble 200 g", 10, 85.0))
    _igual(factura.validar(), [])
    _igual(factura.subtotal(), 1550.0)
    totales = factura.totales()
    _igual(totales["ieps"], 56.0)
    _igual(totales["iva"], 256.96)
    _igual(totales["retencion_isr"], 19.38)
    texto = factura.a_texto()
    assert "A-0001520" in texto


def test_factura_validacion():
    factura = Factura("A", 1, date(2026, 1, 1), RFC_EMPRESA, "XXX", "Público en general", metodo_pago="PPD")
    errores = factura.validar()
    assert "RFC del receptor inválido" in errores
    assert "la factura debe tener al menos un concepto" in errores
    assert any("PPD" in e for e in errores)


# --- nómina ------------------------------------------------------------------

def test_isr_y_nomina():
    _igual(calcular_isr_mensual(10_000), 770.90)
    _igual(calcular_isr_mensual(0), 0.0)
    recibo = calcular_recibo_nomina("Ana López", 12_000)
    _igual(recibo["isr"], 1033.15)
    _igual(recibo["subsidio_empleo"], 0.0)
    _cerca(recibo["neto"], recibo["percepciones"] - recibo["isr_retenido"] - recibo["imss"], 0.011)
    bajo = calcular_recibo_nomina("Luis Pérez", 9_000)
    _igual(bajo["subsidio_empleo"], SUBSIDIO_EMPLEO_MONTO)
    nomina = calcular_nomina([
        {"nombre": "Ana", "salario_mensual": 12_000},
        {"nombre": "Luis", "salario_mensual": 9_000, "horas_extra": 4, "faltas": 1},
    ])
    _igual(len(nomina["recibos"]), 2)
    _cerca(nomina["total_neto"], sum(r["neto"] for r in nomina["recibos"]), 0.011)


def test_vacaciones_y_aguinaldo():
    _igual([dias_vacaciones(a) for a in (0, 1, 3, 5, 6, 10, 11, 16)], [0, 12, 16, 20, 22, 22, 24, 26])
    _igual(aguinaldo(300, 365), 4500.0)
    _igual(aguinaldo(300, 73), 900.0)
    _igual(prima_vacacional(400, 2), 1400.0)


# --- grafos ------------------------------------------------------------------

def test_grafo_recorridos():
    grafo = red_reparto_demo()
    _igual(len(grafo), 8)
    _igual(grafo.grado("Tlaquepaque"), 5)
    _igual(bfs(grafo, "Chapala")[:3], ["Chapala", "El Salto", "Tlajomulco"])
    _igual(dfs(grafo, "Chapala")[:3], ["Chapala", "El Salto", "Tlaquepaque"])
    _igual(camino_menos_saltos(grafo, "Zapopan", "Chapala"), ["Zapopan", "CEDIS", "Tlajomulco", "Chapala"])
    _lanza(ErrorRuta, grafo.agregar_arista, "A", "B", -1)


def test_dijkstra_triangulo():
    grafo = Grafo()
    grafo.agregar_arista("A", "B", 5)
    grafo.agregar_arista("A", "C", 6)
    grafo.agregar_arista("B", "C", 2)
    distancias, _ = dijkstra(grafo, "A")
    _igual(distancias, {"A": 0.0, "B": 5.0, "C": 6.0})


def test_ruta_mas_corta_red_reparto():
    grafo = red_reparto_demo()
    distancias, _ = dijkstra(grafo, "CEDIS")
    _igual(distancias["Guadalajara Centro"], 9.0)
    _igual(distancias["Tlajomulco"], 22.0)
    distancia, ruta = ruta_mas_corta(grafo, "CEDIS", "Chapala")
    _igual(distancia, 51.0)
    _igual(ruta, ["CEDIS", "Tlaquepaque", "El Salto", "Chapala"])
    grafo.agregar_nodo("Isla")
    _lanza(ErrorRuta, ruta_mas_corta, grafo, "CEDIS", "Isla")


def test_plan_de_reparto():
    orden, total = plan_reparto_vecino_mas_cercano(red_reparto_demo(), "CEDIS", ["Tonalá", "Chapala", "Zapopan"])
    _igual(orden, ["Zapopan", "Tonalá", "Chapala"])
    _igual(total, 79.0)


def test_arbol_expansion_minima_y_componentes():
    arbol, total = arbol_expansion_minima(red_reparto_demo())
    _igual(len(arbol), 7)
    _igual(total, 90.0)
    grafo = Grafo()
    grafo.agregar_arista("A", "B")
    grafo.agregar_arista("C", "D")
    grafo.agregar_nodo("E")
    _igual(componentes_conexas(grafo), [["E"], ["A", "B"], ["C", "D"]])


def test_orden_topologico():
    dependencias = {
        "firmar_contrato": [],
        "remodelar_local": ["firmar_contrato"],
        "instalar_refrigeradores": ["remodelar_local"],
        "contratar_personal": ["firmar_contrato"],
        "capacitar_personal": ["contratar_personal"],
        "surtir_inventario": ["instalar_refrigeradores"],
        "inaugurar": ["surtir_inventario", "capacitar_personal"],
    }
    orden = orden_topologico(dependencias)
    posicion = {tarea: i for i, tarea in enumerate(orden)}
    for tarea, previas in dependencias.items():
        for previa in previas:
            assert posicion[previa] < posicion[tarea], f"{previa} debe ir antes que {tarea}"
    _igual(orden[0], "firmar_contrato")
    _igual(orden[-1], "inaugurar")
    _lanza(ErrorRuta, orden_topologico, {"a": ["b"], "b": ["a"]})


# --- evaluador de fórmulas ---------------------------------------------------

def test_evaluador_aritmetica():
    casos = {
        "2 + 3 * 4": 14,
        "(2 + 3) * 4": 20,
        "-2 ^ 2": -4,
        "2 ^ 3 ^ 2": 512,
        "2 ** -1": 0.5,
        "10 % 4 + 7 / 2": 5.5,
        "-(3 - 5) * +2": 4,
        ".5 + 1.": 1.5,
    }
    for expresion, esperado in casos.items():
        _cerca(evaluar_expresion(expresion), esperado, 1e-9, expresion)


def test_evaluador_funciones_y_variables():
    _igual(evaluar_expresion("max(1, 5, 3) + min(4, 2)"), 7.0)
    _igual(evaluar_expresion("abs(-3.5) + raiz(16)"), 7.5)
    _igual(evaluar_expresion("redondear(10 / 3, 2)"), 3.33)
    _igual(evaluar_expresion("max(1, min(8, 3 * 2))"), 6.0)
    _igual(evaluar_expresion("costo * (1 + margen / 100)", {"costo": 80, "margen": 25}), 100.0)
    _igual(variables_de_expresion("costo * (1 + margen / 100) - descuento"), ["costo", "descuento", "margen"])


def test_evaluador_errores():
    for expresion in ("2 +", "(1 + 2", "1 + 2)", "1 / 0", "foo(1)", "x + 1", "2 3", "abs(1, 2)", "", "3 $ 4", "()", "max(1,)"):
        _lanza(ErrorParser, evaluar_expresion, expresion)


def test_precio_por_formula():
    _igual(calcular_precio_por_formula(100), 150.8)
    _igual(calcular_precio_por_formula(80, formula="techo(costo * 1.33)"), 107.0)
    _igual(calcular_precio_por_formula(80, formula="costo + flete", flete=12.5), 92.5)


# --- analítica ---------------------------------------------------------------

def test_resumen_estadistico():
    resumen = resumen_estadistico([10, 20, 30, 40, 51])
    _igual(resumen["n"], 5)
    _igual(resumen["suma"], 151)
    _igual(resumen["promedio"], 30.2)
    _igual(resumen["mediana"], 30.0)
    _igual(resumen_estadistico([]), {"n": 0})


def test_analisis_abc_y_pronostico():
    clasificacion = analisis_abc({"A": 500, "B": 300, "C": 120, "D": 50, "E": 30})
    _igual(clasificacion, {"A": "A", "B": "A", "C": "B", "D": "B", "E": "C"})
    _igual(pronostico_promedio_movil([10, 20, 30, 40], ventana=2, periodos=2), [35.0, 37.5])
    _igual(detectar_anomalias([10, 11, 9, 10, 12, 10, 11, 60]), [7])


def test_ticket_promedio_y_ventas_por_dia():
    ventas = [
        {"fecha": "2026-03-14", "total": 100.0, "lineas": [{"sku": "X", "cantidad": 2}]},
        {"fecha": "2026-03-14", "total": 50.5, "lineas": [{"sku": "Y", "cantidad": 1}, {"sku": "X", "cantidad": 1}]},
        {"fecha": "2026-03-15", "total": 75.0, "lineas": [{"sku": "Y", "cantidad": 4}]},
    ]
    _igual(ticket_promedio(ventas), 75.17)
    _igual(ventas_por_dia(ventas), {"2026-03-14": 150.5, "2026-03-15": 75.0})
    _igual(productos_mas_vendidos(ventas, 2), [("Y", 5), ("X", 3)])


# --- integración -------------------------------------------------------------

def test_simulacion_de_jornada():
    resultado = simular_jornada(semilla=42, num_ventas=30)
    ventas = resultado["ventas"]
    _igual(len(ventas) + resultado["rechazadas"], 30)
    assert len(ventas) >= 20, "la mayoría de las ventas deberían procesarse"
    folios = [v["folio"] for v in ventas]
    _igual(folios, [f"V-{i:06d}" for i in range(1, len(ventas) + 1)])
    for venta in ventas:
        _cerca(venta["total"], venta["subtotal"] + venta["iva"], 0.011, venta["folio"])
    inventario = resultado["inventario"]
    vendidas = unidades_por_producto(ventas)
    for sku in inventario.skus_ordenados():
        inicial = sum(m.cantidad for m in inventario.movimientos_de(sku) if m.referencia == "INV-INICIAL")
        _igual(inventario.existencia(sku), inicial - vendidas.get(sku, 0), f"existencia de {sku}")


def test_repositorio_generico():
    repositorio = RepositorioProveedores()
    eventos = []
    repositorio.suscribir(lambda evento, registro: eventos.append((evento, registro.id)))
    repositorio.agregar_varios(generar_proveedores_demo(12, semilla=5))
    _igual(repositorio.siguiente_id(), 13)
    actualizado = repositorio.actualizar(3, dias_credito=60)
    _igual(actualizado.dias_credito, 60)
    _lanza(ErrorValidacion, repositorio.actualizar, 3, dias_credito=-1)
    _lanza(ErrorSistema, repositorio.actualizar, 3, id=99)
    repositorio.eliminar(12)
    _igual(len(repositorio), 11)
    _lanza(EntidadNoEncontrada, repositorio.obtener, 12)
    _igual(eventos[-2:], [("cambio", 3), ("baja", 12)])
    _igual(len(repositorio.buscar(dias_credito=60)) >= 1, True)
    _lanza(AttributeError, repositorio.buscar, campo_inexistente=1)
    pagina = repositorio.paginar(2, 5)
    _igual([r.id for r in pagina["elementos"]], [6, 7, 8, 9, 10])
    ordenados = repositorio.ordenar_por("limite_credito", descendente=True)
    assert ordenados[0].limite_credito >= ordenados[-1].limite_credito
    copia = RepositorioProveedores()
    copia.importar_json(repositorio.exportar_json())
    _igual(copia.listar(), repositorio.listar())
    _lanza(TypeError, repositorio.agregar, "no soy un proveedor")


def test_cargar_catalogos_demo():
    catalogos = cargar_catalogos_demo(5)
    _igual(set(catalogos), set(CATALOGO_ENTIDADES))
    for nombre, repositorio in catalogos.items():
        _igual(len(repositorio), 5, nombre)


# --- pruebas del catálogo de entidades ---------------------------------------

def test_entidad_proveedor():
    datos = generar_proveedores_demo(15, semilla=100)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Proveedor de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioProveedores()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Proveedor.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioProveedores()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, razon_social="")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_estatus().values()), 15)
    _cerca(repo.total_limite_credito(), sum(r.limite_credito for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Proveedores" in reporte_proveedores(repo)


def test_entidad_categoria():
    datos = generar_categorias_demo(15, semilla=101)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Categoria de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioCategorias()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Categoria.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioCategorias()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, nombre="")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(repo.resumen()["total"], 15)
    assert "Categorías" in reporte_categorias(repo)


def test_entidad_producto():
    datos = generar_productos_demo(15, semilla=102)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Producto de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioProductos()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Producto.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioProductos()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, sku="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_unidad().values()), 15)
    _cerca(repo.total_precio_lista(), sum(r.precio_lista for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Productos" in reporte_productos(repo)


def test_entidad_sucursal():
    datos = generar_sucursales_demo(15, semilla=103)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Sucursal de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioSucursales()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Sucursal.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioSucursales()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, nombre="")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_estado().values()), 15)
    _igual(repo.resumen()["total"], 15)
    assert "Sucursales" in reporte_sucursales(repo)


def test_entidad_empleado():
    datos = generar_empleados_demo(15, semilla=104)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Empleado de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioEmpleados()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Empleado.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioEmpleados()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, nombre="")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_puesto().values()), 15)
    _igual(sum(repo.conteo_por_turno().values()), 15)
    _cerca(repo.total_salario_mensual(), sum(r.salario_mensual for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Empleados" in reporte_empleados(repo)


def test_entidad_cliente():
    datos = generar_clientes_demo(15, semilla=105)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Cliente de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioClientes()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Cliente.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioClientes()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, nombre="")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_tipo().values()), 15)
    _cerca(repo.total_limite_credito(), sum(r.limite_credito for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Clientes" in reporte_clientes(repo)


def test_entidad_promocion():
    datos = generar_promociones_demo(15, semilla=106)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Promocion de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioPromociones()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Promocion.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioPromociones()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, nombre="")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_tipo().values()), 15)
    _cerca(repo.total_compra_minima(), sum(r.compra_minima for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Promociones" in reporte_promociones(repo)


def test_entidad_cupon():
    datos = generar_cupones_demo(15, semilla=107)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Cupon de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioCupones()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Cupon.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioCupones()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, codigo="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(repo.resumen()["total"], 15)
    assert "Cupones" in reporte_cupones(repo)


def test_entidad_pedido():
    datos = generar_pedidos_demo(15, semilla=108)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Pedido de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioPedidos()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Pedido.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioPedidos()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, folio="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_estatus().values()), 15)
    _cerca(repo.total_subtotal(), sum(r.subtotal for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Órdenes de compra" in reporte_pedidos(repo)


def test_entidad_envio():
    datos = generar_envios_demo(15, semilla=109)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Envio de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioEnvios()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Envio.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioEnvios()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, guia="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_transportista().values()), 15)
    _cerca(repo.total_costo(), sum(r.costo for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Envíos" in reporte_envios(repo)


def test_entidad_devolucion():
    datos = generar_devoluciones_demo(15, semilla=110)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Devolucion de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioDevoluciones()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Devolucion.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioDevoluciones()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, folio_venta="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_motivo().values()), 15)
    _cerca(repo.total_monto(), sum(r.monto for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Devoluciones" in reporte_devoluciones(repo)


def test_entidad_almacen():
    datos = generar_almacenes_demo(15, semilla=111)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Almacen de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioAlmacenes()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Almacen.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioAlmacenes()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, clave="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(repo.resumen()["total"], 15)
    assert "Almacenes" in reporte_almacenes(repo)


def test_entidad_vehiculo():
    datos = generar_vehiculos_demo(15, semilla=112)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Vehiculo de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioVehiculos()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Vehiculo.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioVehiculos()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, placas="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_tipo().values()), 15)
    _igual(repo.resumen()["total"], 15)
    assert "Vehículos" in reporte_vehiculos(repo)


def test_entidad_ruta():
    datos = generar_rutas_demo(15, semilla=113)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Ruta de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioRutas()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Ruta.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioRutas()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, clave="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _cerca(repo.total_peaje(), sum(r.peaje for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Rutas" in reporte_rutas(repo)


def test_entidad_turno():
    datos = generar_turnos_demo(15, semilla=114)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Turno de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioTurnos()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Turno.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioTurnos()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, empleado_id=0)
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_tipo().values()), 15)
    _igual(repo.resumen()["total"], 15)
    assert "Turnos" in reporte_turnos(repo)


def test_entidad_venta_registrada():
    datos = generar_ventas_registradas_demo(15, semilla=115)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"VentaRegistrada de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioVentasRegistradas()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(VentaRegistrada.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioVentasRegistradas()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, folio="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_forma_pago().values()), 15)
    _cerca(repo.total_subtotal(), sum(r.subtotal for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Ventas registradas" in reporte_ventas_registradas(repo)


def test_entidad_corte_caja():
    datos = generar_cortes_caja_demo(15, semilla=116)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"CorteCaja de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioCortesCaja()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(CorteCaja.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioCortesCaja()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, sucursal_clave="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _cerca(repo.total_fondo_inicial(), sum(r.fondo_inicial for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Cortes de caja" in reporte_cortes_caja(repo)


def test_entidad_auditoria():
    datos = generar_auditorias_demo(15, semilla=117)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Auditoria de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioAuditorias()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Auditoria.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioAuditorias()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, fecha="31/12/2026")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_accion().values()), 15)
    _igual(repo.resumen()["total"], 15)
    assert "Bitácora de auditoría" in reporte_auditorias(repo)


def test_entidad_mantenimiento():
    datos = generar_mantenimientos_demo(15, semilla=118)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Mantenimiento de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioMantenimientos()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Mantenimiento.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioMantenimientos()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, vehiculo_placas="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_tipo().values()), 15)
    _cerca(repo.total_costo(), sum(r.costo for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Mantenimientos" in reporte_mantenimientos(repo)


def test_entidad_gasto():
    datos = generar_gastos_demo(15, semilla=119)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Gasto de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioGastos()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Gasto.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioGastos()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, concepto="")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_categoria().values()), 15)
    _cerca(repo.total_monto(), sum(r.monto for r in datos), 0.011)
    _igual(repo.resumen()["total"], 15)
    assert "Gastos" in reporte_gastos(repo)


def test_entidad_queja():
    datos = generar_quejas_demo(15, semilla=120)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Queja de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioQuejas()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Queja.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioQuejas()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, cliente_id=0)
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_canal().values()), 15)
    _igual(sum(repo.conteo_por_prioridad().values()), 15)
    _igual(repo.resumen()["total"], 15)
    assert "Quejas" in reporte_quejas(repo)


def test_entidad_lista_precio():
    datos = generar_listas_precios_demo(15, semilla=121)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"ListaPrecio de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioListasPrecios()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(ListaPrecio.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioListasPrecios()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, clave="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_tipo_cliente().values()), 15)
    _igual(sum(repo.conteo_por_moneda().values()), 15)
    _igual(repo.resumen()["total"], 15)
    assert "Listas de precios" in reporte_listas_precios(repo)


def test_entidad_conteo_inventario():
    datos = generar_conteos_inventario_demo(15, semilla=122)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"ConteoInventario de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioConteosInventario()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(ConteoInventario.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioConteosInventario()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, almacen_clave="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(repo.resumen()["total"], 15)
    assert "Conteos de inventario" in reporte_conteos_inventario(repo)


def test_entidad_usuario():
    datos = generar_usuarios_demo(15, semilla=123)
    for registro in datos:
        errores = registro.validar()
        assert errores == [], f"Usuario de demostración inválido (id={registro.id}): {errores}"
    repo = RepositorioUsuarios()
    _igual(repo.agregar_varios(datos), 15)
    primero = repo.obtener(1)
    _igual(Usuario.desde_dict(primero.a_dict()), primero, "ida y vuelta por diccionario")
    copia = RepositorioUsuarios()
    copia.importar_csv(repo.exportar_csv())
    _igual(copia.listar(), repo.listar(), "ida y vuelta por CSV")
    invalido = replace(primero, id=10_000, usuario="???")
    _lanza(ErrorValidacion, repo.agregar, invalido)
    _igual(sum(repo.conteo_por_rol().values()), 15)
    _igual(repo.resumen()["total"], 15)
    assert "Usuarios" in reporte_usuarios(repo)


# ==============================================================================
# SECCIÓN 25. EJECUCIÓN
# ==============================================================================


def _pruebas_registradas(filtro: Optional[str] = None) -> List[Tuple[str, Callable[[], None]]]:
    return [
        (nombre, objeto)
        for nombre, objeto in list(globals().items())
        if nombre.startswith("test_") and callable(objeto) and (filtro is None or filtro in nombre)
    ]


def ejecutar_pruebas(filtro: Optional[str] = None, detallado: bool = False) -> int:
    pruebas = _pruebas_registradas(filtro)
    if not pruebas:
        print(f"No hay pruebas que coincidan con {filtro!r}")
        return 1
    fallas = []
    inicio = datetime.now()
    for nombre, prueba in pruebas:
        try:
            prueba()
        except Exception as exc:  # noqa: BLE001 - se reporta cualquier falla
            marcos = [m for m in traceback.extract_tb(exc.__traceback__) if m.name not in ("_igual", "_cerca", "_lanza")]
            marco = marcos[-1]
            fallas.append((nombre, exc, marco))
            print(f"FALLA  {nombre}")
        else:
            if detallado:
                print(f"ok     {nombre}")
    duracion = (datetime.now() - inicio).total_seconds()
    if fallas:
        print("=" * 78)
        for nombre, exc, marco in fallas:
            print(f"[{nombre}] {type(exc).__name__}: {exc}")
            print(f"    en {marco.name}(), línea {marco.lineno}: {marco.line}")
    print("=" * 78)
    print(f"{len(pruebas) - len(fallas)} de {len(pruebas)} pruebas pasaron en {duracion:.2f} s")
    return 0 if not fallas else 1


def main(argv: Optional[Sequence[str]] = None) -> int:
    argumentos = list(sys.argv[1:] if argv is None else argv)
    if "--demo" in argumentos:
        imprimir_demo()
        return 0
    if "--lista" in argumentos:
        for nombre, _ in _pruebas_registradas():
            print(nombre)
        return 0
    filtro = None
    if "-k" in argumentos:
        indice = argumentos.index("-k")
        if indice + 1 >= len(argumentos):
            print("uso: -k <texto>")
            return 2
        filtro = argumentos[indice + 1]
    return ejecutar_pruebas(filtro, detallado="-v" in argumentos)


if __name__ == "__main__":
    sys.exit(main())
