"""Sistema simulado de gestión de equipos biomédicos para evaluar agentes de IA.

No utilizar para decisiones clínicas ni para controlar equipos reales.
Incluye defectos intencionales para pruebas de debugging.
"""
from __future__ import annotations

import csv
import json
import random
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from statistics import mean
from typing import Any

SEED = 2026
random.seed(SEED)
BASE = Path.cwd()
OUT = BASE / "salida_monitoreo"

@dataclass
class Equipo:
    codigo: str
    nombre: str
    area: str
    fabricante: str
    modelo: str
    estado: str = "activo"
    horas_uso: int = 0
    ultimo_mantenimiento: str = "2026-01-01"
    intervalo_mantenimiento_dias: int = 90

@dataclass
class Lectura:
    codigo_equipo: str
    variable: str
    valor: float
    unidad: str
    momento: str

@dataclass
class Incidencia:
    codigo_equipo: str
    categoria: str
    descripcion: str
    severidad: str
    momento: str
    atendida: bool = False

@dataclass
class OrdenTrabajo:
    folio: str
    codigo_equipo: str
    descripcion: str
    prioridad: str
    creada: str
    cerrada: bool = False

class Inventario:
    def __init__(self) -> None:
        self.equipos: dict[str, Equipo] = {}

    def agregar(self, equipo: Equipo) -> None:
        if equipo.codigo in self.equipos:
            raise ValueError(f"Código duplicado: {equipo.codigo}")
        self.equipos[equipo.codigo] = equipo

    def obtener(self, codigo: str) -> Equipo:
        return self.equipos[codigo]

    def listar(self, area: str | None = None) -> list[Equipo]:
        datos = list(self.equipos.values())
        return [e for e in datos if area is None or e.area == area]

    def cambiar_estado(self, codigo: str, estado: str) -> None:
        if estado not in {"activo", "mantenimiento", "fuera_servicio"}:
            raise ValueError("Estado no válido")
        self.obtener(codigo).estado = estado

class Historial:
    def __init__(self) -> None:
        self.lecturas: list[Lectura] = []
        self.incidencias: list[Incidencia] = []
        self.ordenes: list[OrdenTrabajo] = []

    def agregar_lectura(self, lectura: Lectura) -> None:
        self.lecturas.append(lectura)

    def agregar_incidencia(self, incidencia: Incidencia) -> None:
        self.incidencias.append(incidencia)

    def lecturas_equipo(self, codigo: str, variable: str | None = None) -> list[Lectura]:
        return [x for x in self.lecturas if x.codigo_equipo == codigo and
                (variable is None or x.variable == variable)]

    def incidencias_pendientes(self) -> list[Incidencia]:
        return [i for i in self.incidencias if not i.atendida]

class Monitor:
    LIMITES = {
        "temperatura": (15.0, 35.0, "°C"),
        "bateria": (20.0, 100.0, "%"),
        "vibracion": (0.0, 4.5, "mm/s"),
        "presion": (90.0, 110.0, "kPa"),
    }

    def __init__(self, inventario: Inventario, historial: Historial) -> None:
        self.inventario = inventario
        self.historial = historial

    def evaluar(self, lectura: Lectura) -> bool:
        """Devuelve True si el valor cae fuera de los límites simulados."""
        minimo, maximo, unidad = self.LIMITES[lectura.variable]
        if lectura.unidad != unidad:
            raise ValueError("Unidad incompatible")
        # DEFECTO INTENCIONAL A: se omite la condición de valor inferior al mínimo.
        fuera = lectura.valor > maximo
        if fuera:
            self.historial.agregar_incidencia(Incidencia(
                lectura.codigo_equipo, "alarma",
                f"{lectura.variable} fuera de rango: {lectura.valor} {unidad}",
                "alta", lectura.momento))
        return fuera

    def registrar(self, lectura: Lectura) -> bool:
        self.inventario.obtener(lectura.codigo_equipo)
        self.historial.agregar_lectura(lectura)
        return self.evaluar(lectura)

class Mantenimiento:
    def __init__(self, inventario: Inventario, historial: Historial) -> None:
        self.inventario = inventario
        self.historial = historial

    def dias_desde_servicio(self, equipo: Equipo, hoy: datetime) -> int:
        fecha = datetime.fromisoformat(equipo.ultimo_mantenimiento)
        return (hoy - fecha).days

    def requiere_servicio(self, equipo: Equipo, hoy: datetime) -> bool:
        # DEFECTO INTENCIONAL B: comparación estricta omite el día exacto de vencimiento.
        return self.dias_desde_servicio(equipo, hoy) > equipo.intervalo_mantenimiento_dias

    def pendientes(self, hoy: datetime) -> list[Equipo]:
        return [e for e in self.inventario.listar() if self.requiere_servicio(e, hoy)]

    def abrir_orden(self, equipo: Equipo, hoy: datetime) -> OrdenTrabajo:
        folio = f"OT-{len(self.historial.ordenes)+1:05d}"
        orden = OrdenTrabajo(folio, equipo.codigo, "Mantenimiento preventivo", "media",
                            hoy.isoformat(timespec="seconds"))
        self.historial.ordenes.append(orden)
        return orden

class Reportes:
    def __init__(self, inventario: Inventario, historial: Historial) -> None:
        self.inventario = inventario
        self.historial = historial

    def resumen_areas(self) -> dict[str, int]:
        resultado: dict[str, int] = {}
        for equipo in self.inventario.listar():
            resultado[equipo.area] = resultado.get(equipo.area, 0) + 1
        return resultado

    def promedio(self, codigo: str, variable: str) -> float:
        valores = [x.valor for x in self.historial.lecturas_equipo(codigo, variable)]
        # DEFECTO INTENCIONAL C: falla si todavía no hay lecturas.
        return sum(valores) / len(valores)

    def exportar_json(self, destino: Path) -> None:
        destino.parent.mkdir(parents=True, exist_ok=True)
        datos = {
            "equipos": [asdict(e) for e in self.inventario.listar()],
            "incidencias": [asdict(i) for i in self.historial.incidencias],
            "ordenes": [asdict(o) for o in self.historial.ordenes],
        }
        destino.write_text(json.dumps(datos, ensure_ascii=False, indent=2), encoding="utf-8")

    def exportar_csv(self, destino: Path) -> None:
        destino.parent.mkdir(parents=True, exist_ok=True)
        with destino.open("w", newline="", encoding="utf-8") as archivo:
            writer = csv.writer(archivo)
            writer.writerow(["equipo", "variable", "valor", "unidad", "momento"])
            for x in self.historial.lecturas:
                writer.writerow([x.codigo_equipo, x.variable, x.valor, x.unidad, x.momento])

def crear_inventario() -> Inventario:
    """Genera una flota simulada con distribución reproducible."""
    inventario = Inventario()
    for numero in range(1, 51):
        nombre, fabricante, modelo = tipos_equipo((numero - 1) % 5)
        inventario.agregar(Equipo(
            codigo=f"EQ-{numero:03d}", nombre=nombre,
            area=AREAS[(numero - 1) % len(AREAS)],
            fabricante=fabricante, modelo=modelo,
            horas_uso=numero * 37,
            ultimo_mantenimiento=(datetime(2026, 8, 1) +
                                  timedelta(days=numero % 15)).date().isoformat(),
            intervalo_mantenimiento_dias=60 + (numero % 3) * 30,
        ))
    return inventario

AREAS = ["Urgencias", "Quirófano", "UCI", "Imagenología", "Hospitalización"]
TIPOS = [
    ("Monitor multiparámetro", "Philips", "MX450"),
    ("Ventilador", "Dräger", "Evita V500"),
    ("Bomba de infusión", "B. Braun", "Infusomat"),
    ("Desfibrilador", "ZOLL", "R Series"),
    ("Electrocardiógrafo", "GE", "MAC 2000"),
]

def tipos_equipo(indice: int) -> tuple[str, str, str]:
    return TIPOS[indice]

def generar_lecturas(inventario: Inventario, fecha: datetime, muestras: int = 5) -> list[Lectura]:
    """Produce lecturas sintéticas, nunca datos de pacientes."""
    resultado: list[Lectura] = []
    for equipo in inventario.listar():
        for indice in range(muestras):
            momento = (fecha + timedelta(minutes=indice * 5)).isoformat(timespec="seconds")
            resultado.extend([
                Lectura(equipo.codigo, "temperatura", round(random.gauss(26, 5), 2), "°C", momento),
                Lectura(equipo.codigo, "bateria", round(random.gauss(68, 22), 2), "%", momento),
                Lectura(equipo.codigo, "vibracion", round(max(0, random.gauss(2.4, 1.2)), 2), "mm/s", momento),
                Lectura(equipo.codigo, "presion", round(random.gauss(100, 7), 2), "kPa", momento),
            ])
    return resultado

def ejecutar_simulacion() -> tuple[Inventario, Historial, Reportes]:
    inventario = crear_inventario()
    historial = Historial()
    monitor = Monitor(inventario, historial)
    hoy = datetime(2026, 11, 4, 10, 0)
    for lectura in generar_lecturas(inventario, hoy):
        monitor.registrar(lectura)
    mantenimiento = Mantenimiento(inventario, historial)
    for equipo in mantenimiento.pendientes(hoy):
        mantenimiento.abrir_orden(equipo, hoy)
    reportes = Reportes(inventario, historial)
    return inventario, historial, reportes

def prueba_inventario_cantidad() -> None:
    assert len(crear_inventario().listar()) == 50

def prueba_inventario_duplicado() -> None:
    inv = Inventario()
    e = Equipo("E1", "Monitor", "UCI", "X", "Y")
    inv.agregar(e)
    try:
        inv.agregar(e)
    except ValueError:
        return
    raise AssertionError("Se permitió un código duplicado")

def prueba_cambio_estado() -> None:
    inv = Inventario()
    inv.agregar(Equipo("E1", "Monitor", "UCI", "X", "Y"))
    inv.cambiar_estado("E1", "mantenimiento")
    assert inv.obtener("E1").estado == "mantenimiento"

def prueba_alarma_alta() -> None:
    inv = Inventario()
    inv.agregar(Equipo("E1", "Monitor", "UCI", "X", "Y"))
    monitor = Monitor(inv, Historial())
    assert monitor.registrar(Lectura("E1", "temperatura", 42, "°C", "2026-11-04"))

def prueba_alarma_baja() -> None:
    inv = Inventario()
    inv.agregar(Equipo("E1", "Monitor", "UCI", "X", "Y"))
    monitor = Monitor(inv, Historial())
    assert monitor.registrar(Lectura("E1", "bateria", 5, "%", "2026-11-04")), "Batería baja sin alarma"

def prueba_alarma_normal() -> None:
    inv = Inventario()
    inv.agregar(Equipo("E1", "Monitor", "UCI", "X", "Y"))
    monitor = Monitor(inv, Historial())
    assert not monitor.registrar(Lectura("E1", "temperatura", 25, "°C", "2026-11-04"))

def prueba_mantenimiento_vencimiento() -> None:
    inv = Inventario()
    e = Equipo("E1", "Monitor", "UCI", "X", "Y",
               ultimo_mantenimiento="2026-10-05", intervalo_mantenimiento_dias=30)
    inv.agregar(e)
    assert Mantenimiento(inv, Historial()).requiere_servicio(e, datetime(2026, 11, 4))

def prueba_promedio_sin_datos() -> None:
    inv = Inventario()
    inv.agregar(Equipo("E1", "Monitor", "UCI", "X", "Y"))
    assert Reportes(inv, Historial()).promedio("E1", "temperatura") is None

def prueba_promedio_con_datos() -> None:
    inv = Inventario()
    inv.agregar(Equipo("E1", "Monitor", "UCI", "X", "Y"))
    hist = Historial()
    hist.agregar_lectura(Lectura("E1", "temperatura", 20, "°C", "2026-11-04"))
    hist.agregar_lectura(Lectura("E1", "temperatura", 30, "°C", "2026-11-04"))
    assert Reportes(inv, hist).promedio("E1", "temperatura") == 25

def clasificar_prioridad(severidad: str, horas_pendiente: int) -> str:
    if severidad == "critica" or (severidad == "alta" and horas_pendiente >= 24):
        return "urgente"
    if severidad == "alta" or horas_pendiente >= 72:
        return "alta"
    if severidad == "media":
        return "media"
    return "baja"

def calcular_disponibilidad(equipos: list[Equipo]) -> float | None:
    if not equipos:
        return None
    return round(100 * sum(e.estado == "activo" for e in equipos) / len(equipos), 2)

def agrupar_incidencias(incidencias: list[Incidencia]) -> dict[str, int]:
    grupos: dict[str, int] = {}
    for incidencia in incidencias:
        grupos[incidencia.severidad] = grupos.get(incidencia.severidad, 0) + 1
    return grupos

def ranking_areas(inventario: Inventario, incidencias: list[Incidencia]) -> list[tuple[str, int]]:
    totales: dict[str, int] = {}
    for incidencia in incidencias:
        area = inventario.obtener(incidencia.codigo_equipo).area
        totales[area] = totales.get(area, 0) + 1
    return sorted(totales.items(), key=lambda par: (-par[1], par[0]))

def detectar_tendencia(lecturas: list[Lectura]) -> str:
    if len(lecturas) < 3:
        return "insuficiente"
    valores = [x.valor for x in lecturas]
    cambios = [b - a for a, b in zip(valores, valores[1:])]
    if all(x > 0 for x in cambios):
        return "ascendente"
    if all(x < 0 for x in cambios):
        return "descendente"
    return "variable"

def ventana_movil(lecturas: list[Lectura], ancho: int) -> list[float]:
    if ancho <= 0:
        raise ValueError("La ventana debe ser positiva")
    if len(lecturas) < ancho:
        return []
    valores = [x.valor for x in lecturas]
    return [round(mean(valores[i:i + ancho]), 3)
            for i in range(len(valores) - ancho + 1)]

def indicadores(inventario: Inventario, historial: Historial) -> dict[str, Any]:
    equipos = inventario.listar()
    return {
        "equipos": len(equipos),
        "disponibilidad_pct": calcular_disponibilidad(equipos),
        "incidencias": len(historial.incidencias),
        "incidencias_pendientes": len(historial.incidencias_pendientes()),
        "ordenes_abiertas": sum(not o.cerrada for o in historial.ordenes),
        "areas": sorted({e.area for e in equipos}),
    }

def escenario_01() -> dict[str, Any]:
    """Escenario reproducible 1: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[1 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (1 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S01-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=1 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S01-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 1/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_02() -> dict[str, Any]:
    """Escenario reproducible 2: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[2 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (2 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S02-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=2 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S02-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 2/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_03() -> dict[str, Any]:
    """Escenario reproducible 3: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[3 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (3 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S03-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=3 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S03-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 3/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_04() -> dict[str, Any]:
    """Escenario reproducible 4: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[4 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (4 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S04-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=4 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S04-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 4/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_05() -> dict[str, Any]:
    """Escenario reproducible 5: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[5 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (5 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S05-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=5 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S05-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 5/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_06() -> dict[str, Any]:
    """Escenario reproducible 6: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[6 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (6 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S06-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=6 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S06-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 6/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_07() -> dict[str, Any]:
    """Escenario reproducible 7: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[7 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (7 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S07-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=7 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S07-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 7/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_08() -> dict[str, Any]:
    """Escenario reproducible 8: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[8 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (8 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S08-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=8 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S08-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 8/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_09() -> dict[str, Any]:
    """Escenario reproducible 9: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[9 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (9 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S09-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=9 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S09-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 9/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_10() -> dict[str, Any]:
    """Escenario reproducible 10: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[10 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (10 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S10-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=10 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S10-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 10/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_11() -> dict[str, Any]:
    """Escenario reproducible 11: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[11 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (11 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S11-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=11 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S11-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 11/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_12() -> dict[str, Any]:
    """Escenario reproducible 12: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[12 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (12 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S12-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=12 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S12-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 12/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_13() -> dict[str, Any]:
    """Escenario reproducible 13: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[13 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (13 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S13-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=13 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S13-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 13/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_14() -> dict[str, Any]:
    """Escenario reproducible 14: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[14 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (14 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S14-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=14 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S14-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 14/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_15() -> dict[str, Any]:
    """Escenario reproducible 15: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[15 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (15 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S15-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=15 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S15-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 15/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_16() -> dict[str, Any]:
    """Escenario reproducible 16: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[16 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (16 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S16-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=16 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S16-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 16/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_17() -> dict[str, Any]:
    """Escenario reproducible 17: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[17 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (17 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S17-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=17 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S17-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 17/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)
def escenario_18() -> dict[str, Any]:
    """Escenario reproducible 18: área, disponibilidad y prioridad."""
    inventario = Inventario()
    area = AREAS[18 % len(AREAS)]
    for indice in range(1, 5):
        estado = "activo" if indice != (18 % 4) + 1 else "mantenimiento"
        inventario.agregar(Equipo(
            codigo=f"S18-{indice}", nombre="Monitor", area=area,
            fabricante="Simulado", modelo="T-100", estado=estado,
            horas_uso=18 * indice * 8,
        ))
    historial = Historial()
    fecha = "2026-11-04T12:00:00"
    for indice in range(1, 5):
        codigo = f"S18-{indice}"
        historial.agregar_lectura(Lectura(codigo, "temperatura", 20 + indice + 18/10, "°C", fecha))
        if indice % 2 == 0:
            historial.agregar_incidencia(Incidencia(
                codigo, "inspeccion", "Revisión visual programada", "baja", fecha))
    return indicadores(inventario, historial)

def pruebas_escenarios() -> None:
    for escenario in ESCENARIOS:
        datos = escenario()
        assert datos["equipos"] == 4
        assert datos["disponibilidad_pct"] == 75.0
        assert datos["incidencias"] == 2
        assert datos["incidencias_pendientes"] == 2

ESCENARIOS = [
    escenario_01,
    escenario_02,
    escenario_03,
    escenario_04,
    escenario_05,
    escenario_06,
    escenario_07,
    escenario_08,
    escenario_09,
    escenario_10,
    escenario_11,
    escenario_12,
    escenario_13,
    escenario_14,
    escenario_15,
    escenario_16,
    escenario_17,
    escenario_18,
]

def ejecutar_pruebas() -> int:
    pruebas = [
        prueba_inventario_cantidad,
        prueba_inventario_duplicado,
        prueba_cambio_estado,
        prueba_alarma_alta,
        prueba_alarma_baja,
        prueba_alarma_normal,
        prueba_mantenimiento_vencimiento,
        prueba_promedio_sin_datos,
        prueba_promedio_con_datos,
        pruebas_escenarios,
    ]
    fallas = 0
    for prueba in pruebas:
        try:
            prueba()
            print(f"OK   {prueba.__name__}")
        except Exception as exc:
            fallas += 1
            print(f"FAIL {prueba.__name__}: {type(exc).__name__}: {exc}")
    print(f"Resultado: {len(pruebas)-fallas}/{len(pruebas)} pruebas correctas")
    return fallas

def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Simulador biomédico para evaluación de agentes")
    parser.add_argument("--probar", action="store_true", help="Ejecutar pruebas internas")
    parser.add_argument("--exportar", action="store_true", help="Generar reportes simulados")
    args = parser.parse_args()
    if args.probar:
        raise SystemExit(1 if ejecutar_pruebas() else 0)
    inventario, historial, reportes = ejecutar_simulacion()
    print(json.dumps(indicadores(inventario, historial), ensure_ascii=False, indent=2))
    if args.exportar:
        reportes.exportar_json(OUT / "resumen.json")
        reportes.exportar_csv(OUT / "lecturas.csv")
        print(f"Reportes guardados en {OUT}")

if __name__ == "__main__":
    main()
