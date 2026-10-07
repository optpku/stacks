module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf

/-!
# Representable quotient sheaves of scheme pre-relations
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- A scheme pre-relation has a representable quotient when the underlying presheaf of its
quotient sheaf is representable. -/
abbrev HasRepresentableQuotient {S : Scheme.{u}} (τ : StandardTopology)
    {U : Over S} (P : PreRelation U) : Prop :=
  (P.quotientSheaf (τ.overTopology S)).obj.IsRepresentable

end AlgebraicGeometry.Scheme.PreRelation
