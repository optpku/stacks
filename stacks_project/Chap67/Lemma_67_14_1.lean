module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.KernelAnnihilation
public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap67.Lemma_67_13_3
public import stacks_project.Chap67.Lemma_67_13_4
public import stacks_project.Chap67.Lemma_67_14_1_Quotient

/-!
# Lemma 67.14.1

For a closed immersion of algebraic spaces, the adjunction unit induces
`F / I F ≅ i_* i^* F`, the counit `i^* i_* G ⟶ G` is an isomorphism, and
quasi-coherent pushforward is exact and fully faithful with essential image
the modules annihilated by the kernel ideal sheaf of `i`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- Pushforward of module sheaves along a closed immersion of algebraic spaces is exact. -/
theorem Modules.pushforward_exact (i : Z ⟶ X) [IsClosedImmersion i] :
    exactFunctor Z.Modules X.Modules (Modules.pushforward i) :=
  sorry

/-- Lemma 67.14.1 (1): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, with `I` the kernel of `𝒪_X ⟶ i_* 𝒪_Z`, the adjunction unit
`F ⟶ i_* i^* F` induces an isomorphism `F / I F ≅ i_* i^* F` for every
`𝒪_X`-module `F`. -/
@[stacks 04CJ, instance]
theorem IsClosedImmersion.isIso_quotientByIdealComparison (i : Z ⟶ X)
    [IsClosedImmersion i] (F : X.Modules) :
    IsIso (Modules.quotientByIdealComparison i F) :=
  sorry

/-- Lemma 67.14.1 (2): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the functor `i^*` is a left inverse of `i_*`; equivalently, the
adjunction counit `i^* i_* G ⟶ G` is an isomorphism for every `𝒪_Z`-module `G`. -/
@[stacks 04CJ, instance]
theorem IsClosedImmersion.isIso_modulesAdjunction_counit (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIso (Modules.pullbackPushforwardAdjunction i).counit :=
  sorry

namespace QCoh

/-- Lemma 67.14.1 (3): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the functor `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` is exact. -/
@[stacks 04CJ]
theorem pushforwardExact (i : Z ⟶ X) [IsClosedImmersion i] :
    exactFunctor (QCoh Z) (QCoh X) (pushforward i) :=
  sorry

namespace pushforward

/-- Lemma 67.14.1 (4): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the functor `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` is full. -/
@[stacks 04CJ, instance]
theorem full (i : Z ⟶ X) [IsClosedImmersion i] : (pushforward i).Full :=
  sorry

/-- Lemma 67.14.1 (5): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the functor `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` is faithful. -/
@[stacks 04CJ, instance]
theorem faithful (i : Z ⟶ X) [IsClosedImmersion i] : (pushforward i).Faithful :=
  sorry

end pushforward

/-- Pushforward of quasi-coherent modules along a closed immersion induces a bijection
on morphisms. -/
theorem pushforward_map_bijective (i : Z ⟶ X) [IsClosedImmersion i] (F G : QCoh Z) :
    Function.Bijective fun f : F ⟶ G ↦ (pushforward i).map f :=
  sorry

/-- Lemma 67.14.1 (6): for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, with `I` the kernel of `𝒪_X ⟶ i_* 𝒪_Z`, a quasi-coherent `𝒪_X`-module
lies in the essential image of `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` if and only if it is
annihilated by `I`. -/
@[stacks 04CJ]
theorem mem_essImage_iff_isAnnihilatedByKernel (i : Z ⟶ X) [IsClosedImmersion i]
    (H : QCoh X) :
    (pushforward i).essImage H ↔
      SheafOfModules.IsAnnihilatedByKernel
        (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap i)) H.obj :=
  sorry

/-- A quasi-coherent `𝒪_X`-module lies in the essential image of closed-immersion
pushforward if and only if every local section of the kernel ideal sheaf acts by
zero. -/
theorem mem_essImage_iff_idealSheaf_smul_eq_zero (i : Z ⟶ X)
    [IsClosedImmersion i] (H : QCoh X) :
    (pushforward i).essImage H ↔
      ∀ U : (smallEtaleSite X)ᵒᵖ,
        ∀ s : (Hom.idealSheaf i).val.obj U,
          ∀ m : H.obj.val.obj U,
            ((Hom.idealSheafι i).val.app U s) • m = 0 :=
  sorry

end QCoh

end AlgebraicGeometry.AlgebraicSpace
