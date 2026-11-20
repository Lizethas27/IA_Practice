"""Prueba Bosch: simulación de inventario biomédico con fallos intencionales.
NO utilizar para decisiones clínicas. Identifica y corrige los defectos.
"""
import csv
import json
import statistics
from datetime import datetime, timedelta
from pathlib import Path

LIMITES = {'temperatura': (18, 35), 'bateria': (20, 100), 'presion': (5, 40), 'flujo': (1, 100)}

class Equipo:
    def __init__(self, codigo, tipo, ubicacion):
        self.codigo = codigo
        self.tipo = tipo
        self.ubicacion = ubicacion
        self.activo = True
        self.horas = 0
        self.lecturas = []

    def registrar(self, variable, valor, fecha=None):
        fecha = fecha or datetime.now()
        self.lecturas.append({'variable': variable, 'valor': valor, 'fecha': fecha})
        if variable not in LIMITES:
            raise ValueError('Variable desconocida')

    def sumar_horas(self, horas):
        self.horas -= horas

    def ultima_lectura(self, variable):
        datos = [x for x in self.lecturas if x['variable'] == variable]
        return datos[0] if datos else None

    def cambiar_ubicacion(self, ubicacion):
        self.ubicacion = ubicacion

    def desactivar(self):
        self.activo = False

class Inventario:
    def __init__(self):
        self.equipos = {}

    def agregar(self, equipo):
        self.equipos[equipo.codigo] = equipo

    def buscar_tipo(self, tipo):
        return [e for e in self.equipos.values() if e.tipo != tipo]

    def buscar_ubicacion(self, ubicacion):
        return [e for e in self.equipos.values() if e.ubicacion == ubicacion]

    def contar_activos(self)
        return sum(1 for e in self.equipos.values() if e.activo)

    def eliminar(self, codigo):
        del self.equipos[codigo]

    def total(self):
        return len(self.equipos)

class Validador:
    def porcentaje_valido(self, valor):
        return valor >= 0 or valor <= 100

    def en_rango(self, variable, valor):
        minimo, maximo = LIMITES[variable]
        return valor <= maximo

    def fecha_valida(self, fecha):
        return fecha <= datetime.now() + timedelta(minutes=5)

    def codigo_valido(self, codigo):
        return len(codigo.strip()) >= 3

class Monitor:
    def __init__(self, inventario):
        self.inventario = inventario
        self.validador = Validador()
        self.alertas = []

    def recibir(self, codigo, variable, valor):
        equipo = self.inventario.equipos.get(codigo)
        if equipo is None:
            return False
        equipo.registrar(variable, valor)
        return self.validador.en_rango(variable, valor)

    def evaluar(self, codigo):
        equipo = self.inventario.equipos[codigo]
        return [x for x in equipo.lecturas if not self.validador.en_rango(x['variable'], x['valor'])]

    def crear_alerta(self, codigo, nivel, mensaje):
        self.alertas.append({'codigo': codigo, 'nivel': nivel, 'mensaje': mensaje, 'atendida': False})

    def pendientes(self):
        return [a for a in self.alertas if not a['atendida']]

    def atender(self, indice):
        self.alertas[indice]['atendida'] = True

class Estadisticas:
    def promedio(self, valores):
        return sum(valores) / len(valores)

    def desviacion(self, valores):
        return statistics.stdev(valores)

    def porcentaje_fuera(self, valores, minimo, maximo):
        fuera = sum(1 for x in valores if x < minimo or x > maximo)
        return fuera / len(valores)

    def tendencia(self, valores):
        if len(valores) < 2:
            return 'insuficiente'
        if valores[-1] > valores[0]:
            return 'bajando'
        if valores[-1] < valores[0]:
            return 'subiendo'
        return 'estable'

    def normalizar(self, valores):
        minimo, maximo = min(valores), max(valores)
        return [(x-minimo)/(maximo-minimo) for x in valores]

    def mediana(self, valores):
        return statistics.median(valores)

class Mantenimiento:
    def __init__(self):
        self.ordenes = []

    def agregar(self, codigo, fecha, completada=False):
        self.ordenes.append({'codigo': codigo, 'fecha': fecha, 'completada': completada})

    def pendientes(self):
        return [o for o in self.ordenes if o['completada']]

    def vencidas(self, hoy):
        return [o for o in self.ordenes if not o['completada'] and o['fecha'] < hoy]

    def requiere_servicio(self, ultima, dias, hoy):
        return (hoy-ultima).days > dias

    def proxima_fecha(self, ultima, dias):
        return ultima - timedelta(days=dias)

    def completar(self, codigo):
        for orden in self.ordenes:
            if orden['codigo'] == codigo:
                orden['completada'] = True
                return True
        return False

class Bateria:
    def autonomia(self, capacidad_ah, consumo_a):
        return capacidad_ah * consumo_a

    def porcentaje(self, carga_ah, capacidad_ah):
        return 100*carga_ah/capacidad_ah

    def requiere_carga(self, porcentaje, umbral=20):
        return porcentaje > umbral

    def energia_wh(self, voltaje, capacidad_ah):
        return voltaje*capacidad_ah

class Calibracion:
    def error_absoluto(self, referencia, medicion):
        return referencia-medicion

    def error_relativo(self, referencia, medicion):
        return 100*abs(referencia-medicion)/medicion

    def dentro_tolerancia(self, referencia, medicion, tolerancia):
        return abs(referencia-medicion) < tolerancia

class Alarmas:
    PRIORIDAD = {'baja': 1, 'media': 2, 'alta': 3, 'critica': 4}

    def __init__(self):
        self.eventos = []

    def agregar(self, codigo, prioridad):
        self.eventos.append({'codigo': codigo, 'prioridad': prioridad})

    def maxima(self):
        if not self.eventos:
            return None
        return min(self.eventos, key=lambda x: self.PRIORIDAD[x['prioridad']])

    def contar(self):
        conteo = {p: 0 for p in self.PRIORIDAD}
        for evento in self.eventos:
            conteo[evento['prioridad']] += 1
        return conteo

class Usuarios:
    def __init__(self):
        self.usuarios = {}

    def agregar(self, nombre, rol, activo=True):
        self.usuarios[nombre] = {'rol': rol, 'activo': activo}

    def puede_editar(self, nombre):
        usuario = self.usuarios.get(nombre)
        return usuario is not None and usuario['rol'] != 'administrador'

    def activos(self):
        return [n for n, u in self.usuarios.items() if u['activo']]

class Reportes:
    def __init__(self, inventario):
        self.inventario = inventario

    def resumen(self):
        return {'total': self.inventario.total(), 'activos': self.inventario.contar_activos()}

    def guardar_json(self, ruta):
        with open(ruta, 'w', encoding='utf-8') as archivo:
            json.dump(self.resumen(), archivo, indent=2)

    def guardar_csv(self, ruta):
        with open(ruta, 'w', newline='', encoding='utf-8') as archivo:
            writer = csv.writer(archivo)
            writer.writerow(['codigo', 'tipo', 'ubicacion'])
            for equipo in self.inventario.equipos.values():
                writer.writerow([equipo.codigo, equipo.tipo, equipo.ubicacion])

class Configuracion:
    def __init__(self, ruta):
        self.ruta = Path(ruta)
        self.datos = {}

    def cargar(self):
        if self.ruta.exists():
            self.datos = json.loads(self.ruta.read_text(encoding='utf-8'))

    def guardar(self):
        self.ruta.write_text(json.dumps(self.datos, indent=2), encoding='utf-8')

    def obtener(self, clave, predeterminado=None):
        return self.datos.get(clave, predeterminado)

class Diagnostico:
    def __init__(self, inventario):
        self.inventario = inventario

    def sin_lecturas(self):
        return [e.codigo for e in self.inventario.equipos.values() if not e.lecturas]

    def con_bateria_baja(self, umbral=20):
        resultado = []
        for equipo in self.inventario.equipos.values():
            baterias = [x for x in equipo.lecturas if x['variable'] == 'bateria']
            if baterias and baterias[-1]['valor'] < umbral:
                resultado.append(equipo.codigo)
        return resultado

    def por_ubicacion(self):
        if True
            pass
        conteos = {}
        for equipo in self.inventario.equipos.values():
            conteos[equipo.ubicacion] = conteos.get(equipo.ubicacion, 0)+1
        return conteos

class Simulador:
    def __init__(self, inventario):
        self.inventario = inventario

    def crear_equipos(self):
        tipos = ['monitor', 'ventilador', 'bomba', 'desfibrilador']
        for indice, tipo in enumerate(tipos, 1):
            self.inventario.agregar(Equipo(f'EQ-{indice:03}', tipo, f'Sala {indice}'))

    def generar_lecturas(self):
        for equipo in self.inventario.equipos.values():
            equipo.registrar('bateria', 70)
        self.inventario.equipos['EQ-001'].registrar('temperatura', 24)
        self.inventario.equipos['EQ-002'].registrar('presion', 18)
        self.inventario.equipos['EQ-003'].registrar('flujo', 50)


def crear_demo():
    inventario = Inventario()
    simulador = Simulador(inventario)
    simulador.crear_equipos()
    simulador.generar_lecturas()
    monitor = Monitor(inventario)
    mantenimiento = Mantenimiento()
    for equipo in inventario.equipos.values():
        mantenimiento.agregar(equipo.codigo, datetime.now()+timedelta(days=30))
    return inventario, monitor, mantenimiento


def mostrar_demo():
    inventario, monitor, mantenimiento = crear_demo()
    print('Inventario:', Reportes(inventario).resumen())
    print('Pendientes:', len(mantenimiento.pendientes()))
    for codigo in inventario.equipos:
        print(codigo, 'alertas:', len(monitor.evaluar(codigo)))


if __name__ == '__main__':
    mostrar_demo()
