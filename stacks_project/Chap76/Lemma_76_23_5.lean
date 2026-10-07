module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap76.Theorem_76_22_1

/-!
# Openness of the relative-flatness locus after a finite-type base

If `X` is locally of finite presentation over `Z`, `Y` is locally of finite type
over `Z`, and a finitely presented module on `X` is flat over `Z`, then the
locus of points at which the module is flat over `Y` is open, and it commutes
with arbitrary base change of `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The cospan identity `(pullback.fst (f ≫ h) g ≫ f) ≫ h = pullback.snd (f ≫ h) g ≫ g`
used to induce the comparison `X ×_Z Z' ⟶ Y ×_Z Z'`. -/
theorem overBaseChange_w {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z) :
    (pullback.fst (f ≫ h) g ≫ f) ≫ h = pullback.snd (f ≫ h) g ≫ g :=
  sorry

/-- The comparison morphism `X ×_Z Z' ⟶ Y ×_Z Z'` induced by `f : X ⟶ Y`. -/
noncomputable def overBaseChange {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z) :
    pullback (f ≫ h) g ⟶ pullback h g :=
  pullback.lift (pullback.fst (f ≫ h) g ≫ f) (pullback.snd (f ≫ h) g)
    (overBaseChange_w f h g)

/-- `overBaseChange f h g` is the mediating morphism of the pullback cone
`pullback.fst (f ≫ h) g ≫ f` and `pullback.snd (f ≫ h) g`. -/
theorem overBaseChange_eq {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f h g =
      pullback.lift (pullback.fst (f ≫ h) g ≫ f) (pullback.snd (f ≫ h) g)
        (overBaseChange_w f h g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 76.23.5 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module.
Assume `X` is locally of finite presentation over `Z`, `F` is of finite
presentation, `F` is flat over `Z`, and `Y` is locally of finite type over `Z`.
Then `flatOverLocus F f` is open in `Points X`. -/
@[stacks 05X2]
theorem isOpen_flatOverAt_of_flatOver {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [LocallyOfFiniteType h] (F : X.Modules) [F.IsFinitePresentation]
    (h_flat : flatOver F (f ≫ h)) : IsOpen (flatOverLocus F f) :=
  sorry

/-- Lemma 76.23.5 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module.
Assume `X` is locally of finite presentation over `Z`, `F` is of finite
presentation, `F` is flat over `Z`, and `Y` is locally of finite type over `Z`.
For a morphism `g : Z' ⟶ Z` of algebraic spaces over `S`, the relative-flatness
locus of `(pullback (pullback.fst (f ≫ h) g)).obj F` over `Y ×_Z Z'` is the
inverse image of `flatOverLocus F f` under `Points.map (pullback.fst (f ≫ h) g)`. -/
@[stacks 05X2]
theorem flatOverLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [LocallyOfFiniteType h]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F (f ≫ h)) :
    flatOverLocus ((pullback (pullback.fst (f ≫ h) g)).obj F)
        (overBaseChange f h g) =
      Points.map (pullback.fst (f ≫ h) g) ⁻¹' flatOverLocus F f :=
  sorry

/-- A point of `Points (pullback (f ≫ h) g)` lies in the relative-flatness locus
of the pulled-back module over `overBaseChange f h g` if and only if its image
under `Points.map (pullback.fst (f ≫ h) g)` lies in `flatOverLocus F f`. -/
theorem mem_flatOverLocus_baseChange_eq_preimage {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [LocallyOfFiniteType h]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F (f ≫ h))
    (x' : Points (Limits.pullback (f ≫ h) g)) :
    x' ∈ flatOverLocus ((pullback (pullback.fst (f ≫ h) g)).obj F)
          (overBaseChange f h g) ↔
      Points.map (pullback.fst (f ≫ h) g) x' ∈ flatOverLocus F f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
