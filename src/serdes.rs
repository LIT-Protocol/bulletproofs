use core::{
    fmt::{self, Formatter},
    marker::PhantomData,
};
use group::Group;
use serde::{
    de::{SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::BulletproofCurveArithmetic;

pub struct CurveScalar<C: BulletproofCurveArithmetic> {
    _marker: PhantomData<C>,
}

impl<C: BulletproofCurveArithmetic> CurveScalar<C> {
    pub fn serialize<S: Serializer>(scalar: &C::Scalar, s: S) -> Result<S::Ok, S::Error> {
        let bytes = C::serialize_scalar(scalar);
        if s.is_human_readable() {
            data_encoding::BASE64.encode(&bytes).serialize(s)
        } else {
            let mut tupler = s.serialize_tuple(bytes.len())?;
            for b in bytes {
                tupler.serialize_element(&b)?;
            }
            tupler.end()
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<C::Scalar, D::Error> {
        if d.is_human_readable() {
            let value = String::deserialize(d)?;
            let bytes = data_encoding::BASE64
                .decode(value.as_bytes())
                .map_err(|_| serde::de::Error::custom("invalid base64"))?;
            C::deserialize_scalar(&bytes).map_err(|_| serde::de::Error::custom("invalid scalar"))
        } else {
            struct ScalarVisitor<C: BulletproofCurveArithmetic>(PhantomData<C>);
            impl<'de, C: BulletproofCurveArithmetic> Visitor<'de> for ScalarVisitor<C> {
                type Value = C::Scalar;

                fn expecting(&self, f: &mut Formatter) -> fmt::Result {
                    write!(f, "a sequence of bytes")
                }

                fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where
                    A: SeqAccess<'de>,
                {
                    let mut bytes = Vec::<u8>::with_capacity(C::SCALAR_BYTES);
                    for _ in 0..C::SCALAR_BYTES {
                        bytes.push(
                            seq.next_element()?
                                .ok_or_else(|| serde::de::Error::custom("invalid scalar"))?,
                        );
                    }
                    C::deserialize_scalar(&bytes)
                        .map_err(|_| serde::de::Error::custom("invalid scalar"))
                }
            }
            d.deserialize_tuple(C::SCALAR_BYTES, ScalarVisitor(PhantomData::<C>))
        }
    }
}

pub struct CurvePoint<C: BulletproofCurveArithmetic> {
    _marker: PhantomData<C>,
}

impl<C: BulletproofCurveArithmetic> CurvePoint<C> {
    pub fn serialize<S: Serializer>(scalar: &C::Point, s: S) -> Result<S::Ok, S::Error> {
        let bytes = C::serialize_point(scalar);
        if s.is_human_readable() {
            data_encoding::BASE64.encode(&bytes).serialize(s)
        } else {
            let mut tupler = s.serialize_tuple(bytes.len())?;
            for b in bytes {
                tupler.serialize_element(&b)?;
            }
            tupler.end()
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<C::Point, D::Error> {
        if d.is_human_readable() {
            let value = String::deserialize(d)?;
            let bytes = data_encoding::BASE64
                .decode(value.as_bytes())
                .map_err(|_| serde::de::Error::custom("invalid base64"))?;
            C::deserialize_point(&bytes).map_err(|_| serde::de::Error::custom("invalid point"))
        } else {
            struct PointVisitor<C: BulletproofCurveArithmetic>(PhantomData<C>);
            impl<'de, C: BulletproofCurveArithmetic> Visitor<'de> for PointVisitor<C> {
                type Value = C::Point;

                fn expecting(&self, f: &mut Formatter) -> fmt::Result {
                    write!(f, "a sequence of bytes")
                }

                fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where
                    A: SeqAccess<'de>,
                {
                    let mut bytes = Vec::<u8>::with_capacity(C::POINT_BYTES);
                    for _ in 0..C::POINT_BYTES {
                        bytes.push(
                            seq.next_element()?
                                .ok_or_else(|| serde::de::Error::custom("invalid point"))?,
                        );
                    }
                    C::deserialize_point(&bytes)
                        .map_err(|_| serde::de::Error::custom("invalid point"))
                }
            }
            d.deserialize_tuple(C::POINT_BYTES, PointVisitor(PhantomData::<C>))
        }
    }
}

pub struct CurvePointVec<C: BulletproofCurveArithmetic> {
    _marker: PhantomData<C>,
}

impl<C: BulletproofCurveArithmetic> CurvePointVec<C> {
    pub fn serialize<S: Serializer>(points_vec: &Vec<C::Point>, s: S) -> Result<S::Ok, S::Error> {
        if s.is_human_readable() {
            let mut points = Vec::with_capacity(points_vec.len());
            for point in points_vec {
                points.push(data_encoding::BASE64.encode(&C::serialize_point(point)));
            }
            points.serialize(s)
        } else {
            let mut bytes = Vec::<u8>::with_capacity(points_vec.len() * C::POINT_BYTES);
            for point in points_vec {
                bytes.append(&mut C::serialize_point(point));
            }
            s.serialize_bytes(&bytes)
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<C::Point>, D::Error> {
        if d.is_human_readable() {
            let points = Vec::<String>::deserialize(d)?;
            let mut result = vec![C::Point::identity(); points.len()];
            for (p, b64) in result.iter_mut().zip(points.iter()) {
                let bytes = data_encoding::BASE64
                    .decode(b64.as_bytes())
                    .map_err(|_| serde::de::Error::custom("invalid base64"))?;
                *p = C::deserialize_point(&bytes)
                    .map_err(|_| serde::de::Error::custom("invalid point"))?;
            }
            Ok(result)
        } else {
            let bytes = Vec::<u8>::deserialize(d)?;
            if bytes.len() % C::POINT_BYTES != 0 {
                return Err(serde::de::Error::custom("invalid bytes length"));
            }
            let mut pos = &bytes[..];
            let mut result = vec![C::Point::identity(); bytes.len() / C::POINT_BYTES];
            for p in result.iter_mut() {
                *p = C::deserialize_point(&pos[..C::POINT_BYTES])
                    .map_err(|_| serde::de::Error::custom("invalid point"))?;
                pos = &pos[C::POINT_BYTES..];
            }
            Ok(result)
        }
    }
}
