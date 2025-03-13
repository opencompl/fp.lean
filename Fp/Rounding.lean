import Fp.Basic

inductive RoundingMode : Type
| RNE : RoundingMode -- RoundNearestTiesToEven
| RNA : RoundingMode -- RoundNearestTiesToAway
| RTP : RoundingMode -- RoundTowardPositive
| RTN : RoundingMode -- RoundTowardNegative
| RTZ : RoundingMode -- RoundTowardZero

-- TODO: Implement different rounding modes
def round (exWidth sigWidth : Nat)
  : EFixedPoint width exOffset -> PackedFloat exWidth sigWidth
  | EFixedPoint.NaN => PackedFloat.getNaN _ _
  | EFixedPoint.Infinity sign => PackedFloat.getInfinity _ _ sign
  | EFixedPoint.Number x =>
  sorry
