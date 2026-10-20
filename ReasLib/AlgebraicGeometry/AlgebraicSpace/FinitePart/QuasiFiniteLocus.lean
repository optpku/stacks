module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.QuasiFinite

/-! # Finite-part sheaves on the quasi-finite locus -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical comparison of finite-part sheaves along the quasi-finite
locus of `f`. -/
def finitePartQuasiFiniteLocusMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    finitePartSheaf ((quasiFiniteLocus f).ι ≫ f) ⟶ finitePartSheaf f :=
  finitePartOpenMap (quasiFiniteLocus f).ι rfl

/-- The comparison from the quasi-finite locus is surjective on finite-part
sections over every test scheme. -/
theorem finitePartQuasiFiniteLocusMap_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (T : (Over S)ᵒᵖ) :
    Function.Surjective
      fun (p : FinitePart.Point ((quasiFiniteLocus f).ι ≫ f) T.unop) ↦
        FinitePart.Point.map (quasiFiniteLocus f).ι rfl p :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, the canonical
comparison from the finite-part sheaf of its quasi-finite locus to its
finite-part sheaf is an isomorphism. -/
instance instIsIso_finitePartQuasiFiniteLocusMap {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    IsIso (finitePartQuasiFiniteLocusMap f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
