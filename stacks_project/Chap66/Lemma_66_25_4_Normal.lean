module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal

@[expose] public section

universe u

/-! Compatibility checks for the normal algebraic-space API. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsNormal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    AlgebraicGeometry.AlgebraicSpace S → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.IsNormal.spec :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsNormal X],
    AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale
      (AlgebraicGeometry.Scheme.isNormal :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u}) X)
#check (AlgebraicGeometry.AlgebraicSpace.IsNormal.of :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X : AlgebraicGeometry.AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.existsSurjectiveEtale
      (AlgebraicGeometry.Scheme.isNormal :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u}) X →
      AlgebraicGeometry.AlgebraicSpace.IsNormal X)
#check (AlgebraicGeometry.AlgebraicSpace.IsNormal.ofOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T : CategoryTheory.Over S},
    AlgebraicGeometry.Scheme.isNormal T.left →
      AlgebraicGeometry.AlgebraicSpace.IsNormal
        (AlgebraicGeometry.AlgebraicSpace.ofOver T))
#check (AlgebraicGeometry.AlgebraicSpace.isNormal_iff_forallEtale :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsNormal X ↔
      AlgebraicGeometry.AlgebraicSpace.forallEtale
        (AlgebraicGeometry.Scheme.isNormal :
          CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u}) X)
