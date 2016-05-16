use unit::Unit;
use uval::UnitValue;
use value::Value;
use rational::Rational;

use std::fmt;
use std::fmt::Write;

use phf;

// I'm only doing the common units here; it'd take a while to type out all the uncommon ones
const DIMENSIONLESS: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const LENGTH: Unit = Unit {m: Rational {num: 1, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const MASS: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const TIME: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 1, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const CURRENT: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 1, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const TEMPERATURE: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 1, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const INTENSITY: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 1, den: 1}, mol: Rational {num: 0, den: 1}};
const AMOUNT: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 1, den: 1}};
const FREQUENCY: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: -1, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const FORCE: Unit = Unit {m: Rational {num: 1, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const PRESSURE: Unit = Unit {m: Rational {num: -1, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const ENERGY: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const POWER: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -3, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const CHARGE: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 1, den: 1}, a: Rational {num: 1, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const VOLTAGE: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -3, den: 1}, a: Rational {num: -1, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const CAPACITANCE: Unit = Unit {m: Rational {num: -2, den: 1}, kg: Rational {num: -1, den: 1}, s: Rational {num: 4, den: 1}, a: Rational {num: 2, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const RESISTANCE: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -3, den: 1}, a: Rational {num: -2, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const MAG_FIELD: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: -1, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};

const AREA: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const VOLUME: Unit = Unit {m: Rational {num: 3, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};

const C_UNITS: Unit = Unit {m: Rational {num: 1, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: -1, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const GC_UNITS: Unit = Unit {m: Rational {num: 3, den: 1}, kg: Rational {num: -1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const H_UNITS: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -1, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const MU0_UNITS: Unit = Unit {m: Rational {num: 1, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: -2, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const EP0_UNITS: Unit = Unit {m: Rational {num: -3, den: 1}, kg: Rational {num: -1, den: 1}, s: Rational {num: 4, den: 1}, a: Rational {num: 2, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const KE_UNITS: Unit = Unit {m: Rational {num: 3, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -4, den: 1}, a: Rational {num: -2, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const NA_UNITS: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 0, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: -1, den: 1}};
const KB_UNITS: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: -1, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};
const F_UNITS: Unit = Unit {m: Rational {num: 0, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: 1, den: 1}, a: Rational {num: 1, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: -1, den: 1}};
const R_UNITS: Unit = Unit {m: Rational {num: 2, den: 1}, kg: Rational {num: 1, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: -1, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: -1, den: 1}};
const G_UNITS: Unit = Unit {m: Rational {num: 1, den: 1}, kg: Rational {num: 0, den: 1}, s: Rational {num: -2, den: 1}, a: Rational {num: 0, den: 1}, k: Rational {num: 0, den: 1}, cd: Rational {num: 0, den: 1}, mol: Rational {num: 0, den: 1}};

const ONE: Value = Value::Exact(Rational {num: 1, den: 1});

macro_rules! num {
    (E $a:expr, $b:expr) => (Value::Exact(Rational {num: $a, den: $b}));
    (I $a:expr) => (Value::Inexact($a));
}

static UNITS: phf::Map<&'static str, UnitValue> = phf_map! {
    "m" => UnitValue {unit: LENGTH, value: ONE},
    "kg" => UnitValue {unit: MASS, value: ONE},
    "s" => UnitValue {unit: TIME, value: ONE},
    "A" => UnitValue {unit: CURRENT, value: ONE},
    "K" => UnitValue {unit: TEMPERATURE, value: ONE},
    "cd" => UnitValue {unit: INTENSITY, value: ONE},
    "mol" => UnitValue {unit: AMOUNT, value: ONE},
    "Hz" => UnitValue {unit: FREQUENCY, value: ONE},
    "rad" => UnitValue {unit: DIMENSIONLESS, value: ONE},
    "sr" => UnitValue {unit: DIMENSIONLESS, value: ONE},
    "N" => UnitValue {unit: FORCE, value: ONE},
    "Pa" => UnitValue {unit: PRESSURE, value: ONE},
    "J" => UnitValue {unit: ENERGY, value: ONE},
    "W" => UnitValue {unit: POWER, value: ONE},
    "C" => UnitValue {unit: CHARGE, value: ONE},
    "V" => UnitValue {unit: VOLTAGE, value: ONE},
    "F" => UnitValue {unit: CAPACITANCE, value: ONE},
    "ohm" => UnitValue {unit: RESISTANCE, value: ONE},
    "T" => UnitValue {unit: MAG_FIELD, value: ONE},
    // customary
    // length
    "in" => UnitValue {unit: LENGTH, value: num!(E 127,5000)},
    "ft" => UnitValue {unit: LENGTH, value: num!(E 381,1250)},
    "yd" => UnitValue {unit: LENGTH, value: num!(E 1143,1250)},
    "mi" => UnitValue {unit: LENGTH, value: num!(E 201168,125)},
    "rd" => UnitValue {unit: LENGTH, value: num!(E 12573,2500)},
    "fur" => UnitValue {unit: LENGTH, value: num!(E 25146,125)},
    "lea" => UnitValue {unit: LENGTH, value: num!(E 25146,125)},
    "nm" => UnitValue {unit: LENGTH, value: num!(E 1852,1)},
    // area
    "ac" => UnitValue {unit: AREA, value: num!(I 4046.8564224)},
    "acre" => UnitValue {unit: AREA, value: num!(E 13641953,3371)},
    // volume (denominator won't fit)
    "gal" => UnitValue {unit: VOLUME, value: num!(I 0.003785411784)},
    "qt"  => UnitValue {unit: VOLUME, value: num!(I 0.000946352946)},
    "pt"  => UnitValue {unit: VOLUME, value: num!(I 0.000473176473)},
    "cup" => UnitValue {unit: VOLUME, value: num!(I 0.0002365882365)},
    "floz" => UnitValue {unit: VOLUME, value: num!(I 0.0000295735295625)},
    "tbsp" => UnitValue {unit: VOLUME, value: num!(I 0.00001478676478125)},
    "tsp" =>  UnitValue {unit: VOLUME, value: num!(I 0.00000492892159375)},
    // mass
    "lb" => UnitValue {unit: MASS, value: num!(I 0.45359237)},
    "oz" => UnitValue {unit: MASS, value: num!(I 0.02834952312)},
    "ton" => UnitValue {unit: MASS, value: num!(I 907.18474)},
    // misc
    "btu" => UnitValue {unit: ENERGY, value: num!(I 1055.056)}, // using ISO definition
    "cal" => UnitValue {unit: ENERGY, value: num!(I 4.184)},
    "Cal" => UnitValue {unit: ENERGY, value: num!(I 4184.0)},
    "hp" => UnitValue {unit: ENERGY, value: num!(I 745.7)},
    // metric
    "ha" => UnitValue {unit: AREA, value: num!(E 10000,1)},
    // t is too easy to accidentally type
    "mt" => UnitValue {unit: MASS, value: num!(E 1000,1)},
    "tonne" => UnitValue {unit: MASS, value: num!(E 1000,1)},
    "L" => UnitValue {unit: VOLUME, value: num!(E 1,1000)},
    "ml" => UnitValue {unit: VOLUME, value: num!(E 1,1000000)},
    "mL" => UnitValue {unit: VOLUME, value: num!(E 1,1000000)},
    "cm" => UnitValue {unit: LENGTH, value: num!(E 1,100)},
    "mm" => UnitValue {unit: LENGTH, value: num!(E 1,1000)},
    "km" => UnitValue {unit: LENGTH, value: num!(E 1000,1)},
    "atm" => UnitValue {unit: PRESSURE, value: num!(I 101325.0)},
    "bar" => UnitValue {unit: PRESSURE, value: num!(E 100000,1)},
    // degrees
    "deg" => UnitValue {unit: DIMENSIONLESS, value: num!(I 0.0174532925199432957)},
    // time
    "min" => UnitValue {unit: TIME, value: num!(E 60,1)},
    "hr" => UnitValue {unit: TIME, value: num!(E 3600,1)},
    "day" => UnitValue {unit: TIME, value: num!(E 86400,1)},
    "amu" => UnitValue {unit: MASS, value: num!(I 1.66053892173e-27)}, // actually u, but u is easy to mistype
    // CONSTANTS
    "_c" => UnitValue {unit: C_UNITS, value: num!(E 299792458,1)},
    "_G" => UnitValue {unit: GC_UNITS, value: num!(I 6.6740831e-11)},
    "_h" => UnitValue {unit: H_UNITS, value: num!(I 6.62607004081e-34)},
    "_mu0" => UnitValue {unit: MU0_UNITS, value: num!(I 1.256637061e-6)},
    "_ep0" => UnitValue {unit: EP0_UNITS, value: num!(I 8.854187817e-12)},
    "_ke" => UnitValue {unit: KE_UNITS, value: num!(I 8.987551787e9)},
    "_e" => UnitValue {unit: CHARGE, value: num!(I 1.60217656535e-19)},
    "_me" => UnitValue {unit: MASS, value: num!(I 9.1093829140e-31)},
    "_mp" => UnitValue {unit: MASS, value: num!(I 1.67262177774e-27)},
    "_NA" => UnitValue {unit: NA_UNITS, value: num!(I 6.0221412927e23)},
    "_kB" => UnitValue {unit: KB_UNITS, value: num!(I 1.380648813e-23)},
    "_F" => UnitValue {unit: F_UNITS, value: num!(I 96485.336521)},
    "_R" => UnitValue {unit: R_UNITS, value: num!(I 8.314462175)},
    "_g" => UnitValue {unit: G_UNITS, value: num!(I 9.807)},
};

// "easy-to-read" hex hash
// units are:
// * 0 (nothing)
// * m
// * kg
// * s
// * A
// * K
// * cd
// * mol
//
// 0-9 are positive, and
// A-F are -1 through -6
static LOOKUP: phf::Map<u32, &'static str> = phf_map! {
//  0x0mksAKcm
    0x000A0000u32 => "Hz",
    0x011B0000u32 => "N",
    0x0A1B0000u32 => "Pa",
    0x021B0000u32 => "J",
    0x021C0000u32 => "J",
    0x00011000u32 => "C",
    0x021CA000u32 => "V",
    0x0BA42000u32 => "F",
    0x021CB000u32 => "ohm",
    0x001BA000u32 => "T",
};

pub fn get(key: &str) -> Option<UnitValue> {
    UNITS.get(key).cloned()
}

fn as_int(r: &Rational) -> Result<u8, ()> {
    if !r.is_integer() { return Err(()); }
    match r.num {
        a @ 0 ... 9 => Ok(a as u8),
        a @ -6 ... -1 => Ok((9 - a) as u8),
        _ => Err(()),
    }
}

fn u_hash(u: &Unit) -> Result<u32, ()> {
    Ok(
        (try!(as_int(&u.m  )) as u32) << 24 |
        (try!(as_int(&u.kg )) as u32) << 20 |
        (try!(as_int(&u.s  )) as u32) << 16 |
        (try!(as_int(&u.a  )) as u32) << 12 |
        (try!(as_int(&u.k  )) as u32) << 8  |
        (try!(as_int(&u.cd )) as u32) << 4  |
        (try!(as_int(&u.mol)) as u32) << 0  |
        0
    )
}

macro_rules! fmt_unit {
    ($u:expr, $name:expr, $num:ident, $den:ident) => {
        if !$u.is_negative() {
            if $u.is_one() {
                $num.push_str($name);
                $num.push(' ');
            } else if !$u.is_zero() {
                write!($num, "{}^{} ", $name, $u);
            }
        } else {
            let neg = -$u;
            if neg.is_one() {
                $den.push_str($name);
                $den.push(' ');
            } else if !neg.is_zero() {
                write!($den, "{}^{} ", $name, neg);
            }
        }
    }
}

impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match u_hash(self).ok().and_then(|a| LOOKUP.get(&a)) {
            Some(a) => write!(f, "{}", a),
            None => {
                let mut num = String::new();
                let mut den = String::new();
                fmt_unit!(self.kg, "kg", num, den);
                fmt_unit!(self.m, "m", num, den);
                fmt_unit!(self.s, "s", num, den);
                fmt_unit!(self.a, "A", num, den);
                fmt_unit!(self.mol, "mol", num, den);
                fmt_unit!(self.k, "K", num, den);
                fmt_unit!(self.cd, "cd", num, den);
                match (num.is_empty(), den.is_empty()) {
                    (true, true) => write!(f, ""),
                    (true, false) => write!(f, "/ {}", den.trim_right()),
                    (false, true) => write!(f, "{}", num.trim_right()),
                    (false, false) => write!(f, "{}/ {}", num, den.trim_right()),
                }
            },
        }
    }
}
