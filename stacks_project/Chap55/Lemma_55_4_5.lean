module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.PicardClassification

/- Lemma 55.4.5. If the genus of a numerical type is nonpositive, its Picard
group is additively equivalent to the integers. -/
@[stacks 0C7K] #check
  (NumericalType.existsIntAddEquivPicardGroup_of_genus_le_zero :
    ∀ (T : NumericalType) (hgenus : T.genus ≤ 0), Nonempty (ℤ ≃+ T.PicardGroup))
