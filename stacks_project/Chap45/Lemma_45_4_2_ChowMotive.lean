module

public import ReasLib.AlgebraicGeometry.ChowMotive

@[expose] public section

open CategoryTheory

universe w v u

variable (k : Type u) [Field k]
variable (GradedCorrespondence : Type u → Type v)
variable [Category.{w} (GradedCorrespondence k)]

#check (ChowMotive.isIdempotentComplete k GradedCorrespondence :
  IsIdempotentComplete (ChowMotive k GradedCorrespondence))
