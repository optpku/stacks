module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Representable

/-!
# Compatibility checks for representable quotient predicates
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- The pre-relation quotient predicates remain available from their shared owner. -/
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.HasAlgebraicSpaceQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
    AlgebraicSpace.PreRelation U → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.HasRepresentableQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
    AlgebraicSpace.PreRelation U → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.hasRepresentableQuotient_iff_exists_ofOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicSpace.PreRelation U),
    AlgebraicSpace.PreRelation.HasRepresentableQuotient P ↔
      ∃ T : Over S, Nonempty
        (AlgebraicSpace.toSheaf.obj (AlgebraicSpace.ofOver T) ≅ P.quotientSheaf))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.hasAlgebraicSpaceQuotient_of_hasRepresentableQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : AlgebraicSpace.PreRelation U),
    AlgebraicSpace.PreRelation.HasRepresentableQuotient P →
      AlgebraicSpace.PreRelation.HasAlgebraicSpaceQuotient P)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.HasAlgebraicSpaceQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
    AlgebraicGeometry.GroupoidAlgebraicSpace B → Prop)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.HasRepresentableQuotient :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
    AlgebraicGeometry.GroupoidAlgebraicSpace B → Prop)
