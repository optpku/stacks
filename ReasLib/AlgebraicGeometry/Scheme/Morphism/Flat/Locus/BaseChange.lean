module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.BaseChange

/-!
# Base change of scheme-morphism flatness loci

This module records openness and arbitrary-base-change compatibility for pointwise flatness
loci of scheme morphisms under relative finiteness and flatness hypotheses.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Let `X` and `Y` be `S`-schemes, with `X` locally of finite presentation and flat over
`S`, and `Y` locally of finite type over `S`. The locus where an `S`-morphism `f : X ⟶ Y`
is flat at a point is open in `X`. -/
theorem isOpen_flatAt {S : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [Flat X.hom] [LocallyOfFiniteType Y.hom] :
    IsOpen {x : X.left | Scheme.Hom.flatAt f.left x} := sorry

/-- Let `X` and `Y` be `S`-schemes, with `X` locally of finite presentation and flat over
`S`, and `Y` locally of finite type over `S`. The pointwise flatness locus of an
`S`-morphism `f : X ⟶ Y` pulls back along every morphism `S' ⟶ S`. -/
theorem flatAt_baseChange_eq_preimage {S S' : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [Flat X.hom] [LocallyOfFiniteType Y.hom]
    (s : S' ⟶ S) :
    {x' : ((Over.pullback s).obj X).left |
        Scheme.Hom.flatAt ((Over.pullback s).map f).left x'} =
      (pullback.fst X.hom s).base ⁻¹' {x : X.left | Scheme.Hom.flatAt f.left x} := sorry

end AlgebraicGeometry.Scheme.Hom
