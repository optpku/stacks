module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For proper morphisms `X ⟶ S` and `Y ⟶ S`, with `X ⟶ S` flat,
an isomorphism on the fibre over `s` extends to an isomorphism after base change
to some open neighbourhood of `s` in `S`. -/
theorem exists_isIso_baseChange_of_isIso_fiber
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (p : X ⟶ Y)
    (sq : CommSq p f g (𝟙 S)) (s : S)
    [IsNoetherian S] [IsProper f] [IsProper g] [Flat f]
    [IsIso (Scheme.Hom.fiberMap f p (𝟙 S) g sq s)] :
    ∃ U : S.Opens, s ∈ U ∧
      IsIso
        (pullback.map f U.ι g U.ι p (𝟙 _) (𝟙 _)
          sq.w.symm
          ((Category.comp_id U.ι).trans (Category.id_comp U.ι).symm)) := sorry

end AlgebraicGeometry.Scheme.Hom
