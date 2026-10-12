/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.LeftDerived

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CharacterHomologyEvaluation

variable {Λ : Type u} [CommRing Λ]

/-- Dualize the actual differentials, reversing their order. -/
def dualShort (S : ShortComplex (ModuleCat.{v} Λ)) :
    ShortComplex (ModuleCat.{v} Λ) :=
  ShortComplex.moduleCatMk (CharacterModule.dual S.g.hom)
    (CharacterModule.dual S.f.hom) (by
      ext χ x
      change χ (S.g (S.f x)) = 0
      rw [S.moduleCat_zero_apply, map_zero])

/-- Choose a cycle representative through the standard kernel/range description.
Only representatives are chosen, never a comparison isomorphism. -/
def representative (S : ShortComplex (ModuleCat.{v} Λ)) (x : S.homology) :
    LinearMap.ker S.g.hom :=
  Quotient.out (S.moduleCatHomologyIso.hom x)

theorem representative_spec (S : ShortComplex (ModuleCat.{v} Λ)) (x : S.homology) :
    (LinearMap.range S.moduleCatToCycles).mkQ (representative S x) =
      S.moduleCatHomologyIso.hom x := by
  exact Quotient.out_eq _

/-- Evaluation on actual representatives of dual cocycles and cycles. -/
def value (S : ShortComplex (ModuleCat.{v} Λ))
    (χ : (dualShort S).homology) (x : S.homology) : AddCircle (1 : ℚ) :=
  (show CharacterModule S.X₂ from (representative (dualShort S) χ).val)
    (representative S x).val

/-- Boundaries pair trivially with cocycles, and coboundaries with cycles.
This is the representative-independence obligation for the displayed map. -/
theorem value_eq (S : ShortComplex (ModuleCat.{v} Λ))
    (χ : (dualShort S).homology) (x : S.homology)
    (c : LinearMap.ker (dualShort S).g.hom) (z : LinearMap.ker S.g.hom)
    (hc : (LinearMap.range (dualShort S).moduleCatToCycles).mkQ c =
      (dualShort S).moduleCatHomologyIso.hom χ)
    (hz : (LinearMap.range S.moduleCatToCycles).mkQ z =
      S.moduleCatHomologyIso.hom x) : value S χ x =
      (show CharacterModule S.X₂ from c.val) z.val := by
  sorry

/-- The character of homology induced by a dual cocycle. -/
def character (S : ShortComplex (ModuleCat.{v} Λ))
    (χ : (dualShort S).homology) : CharacterModule S.homology where
  toFun := value S χ
  map_zero' := by sorry
  map_add' := by sorry

/-- The actual evaluation map, not an independently chosen isomorphism. -/
def evaluation (S : ShortComplex (ModuleCat.{v} Λ)) :
    (dualShort S).homology →ₗ[Λ] CharacterModule S.homology where
  toFun := character S
  map_add' := by sorry
  map_smul' := by sorry

/-- Exactness of characters into the injective abelian group Q/Z identifies
dual homology with the character module of homology. No finiteness is needed. -/
theorem evaluation_bijective (S : ShortComplex (ModuleCat.{v} Λ)) :
    Function.Bijective (evaluation S) := by
  sorry

def evaluationEquiv (S : ShortComplex (ModuleCat.{v} Λ)) :
    (dualShort S).homology ≃ₗ[Λ] CharacterModule S.homology :=
  LinearEquiv.ofBijective (evaluation S) (evaluation_bijective S)

/-- Dualize a specified map of short complexes, with all components given by
precomposition. -/
def dualShortMap {S T : ShortComplex (ModuleCat.{v} Λ)} (f : S ⟶ T) :
    dualShort T ⟶ dualShort S where
  τ₁ := ModuleCat.ofHom (CharacterModule.dual f.τ₃.hom)
  τ₂ := ModuleCat.ofHom (CharacterModule.dual f.τ₂.hom)
  τ₃ := ModuleCat.ofHom (CharacterModule.dual f.τ₁.hom)
  comm₁₂ := by sorry
  comm₂₃ := by sorry

/-- Evaluation is natural for actual chain maps. In particular this handles
comparison maps between projective resolutions, not independently chosen isos. -/
theorem evaluation_naturality {S T : ShortComplex (ModuleCat.{v} Λ)} (f : S ⟶ T) :
    (evaluation S).comp (ShortComplex.homologyMap (dualShortMap f)).hom =
      (CharacterModule.dual (ShortComplex.homologyMap f).hom).comp
        (evaluation T) := by
  sorry

end CharacterHomologyEvaluation
