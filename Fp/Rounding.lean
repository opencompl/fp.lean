import Fp.Basic

inductive RoundingMode : Type
| RNE : RoundingMode -- RoundNearestTiesToEven
| RNA : RoundingMode -- RoundNearestTiesToAway
| RTP : RoundingMode -- RoundTowardPositive
| RTN : RoundingMode -- RoundTowardNegative
| RTZ : RoundingMode -- RoundTowardZero

-- TODO: Implement different rounding modes
def round (exWidth sigWidth : Nat)
  : EFixedPoint width exOffset -> PackedFloat exWidth sigWidth :=
  sorry
