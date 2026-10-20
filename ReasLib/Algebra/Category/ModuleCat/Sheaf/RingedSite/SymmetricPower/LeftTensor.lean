module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.LeftTensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Left tensor maps for symmetric powers on ringed sites

This file transports the sectionwise symmetric left-tensor map through canonical monoidal module
sheafification.  It is stated for arbitrary commutative ringed sites; geometric categories only
need thin specializations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- Lemma 17.21.1 (01CG): the canonical morphism
`F ⊗ Sym^n(G) ⟶ Sym^(n + 1)(G)` on a commutative ringed site induced by `f : F ⟶ G`. -/
@[stacks 01CG "symmetric left tensor map on a ringed site"]
noncomputable def leftTensorMap
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) :
    tensorObj F (sheaf 𝒪 G n) ⟶ sheaf 𝒪 G (n + 1) :=
  tensorHom (moduleSheafificationValIso 𝒪 F).inv (𝟙 (sheaf 𝒪 G n)) ≫
    (ModuleSheafification.tensorIso 𝒪 F.val (presheaf 𝒪 G n)).hom ≫
    (moduleSheafification 𝒪).map
      (PresheafOfModules.SymmetricPower.leftTensorHom 𝒪.obj f.val n)

/-- Naturality of the symmetric left-tensor sheaf morphism in a commuting square. -/
theorem leftTensorMap_naturality
    {F₁ F₂ G₁ G₂ : ringedSiteModuleCategory J 𝒪}
    (a : F₁ ⟶ F₂) (b : G₁ ⟶ G₂) (f₁ : F₁ ⟶ G₁) (f₂ : F₂ ⟶ G₂)
    (h : a ≫ f₂ = f₁ ≫ b) (n : ℕ) :
    tensorHom a (map 𝒪 b n) ≫ leftTensorMap 𝒪 f₂ n =
      leftTensorMap 𝒪 f₁ n ≫ map 𝒪 b (n + 1) := sorry

/-- A symmetric-power sheaf map annihilates the preceding left-tensor map whenever the
underlying module-sheaf composite vanishes. -/
theorem leftTensorMap_comp_eq_zero
    {F G H : ringedSiteModuleCategory J 𝒪}
    (n : ℕ) {f : F ⟶ G} {g : G ⟶ H} (hfg : f ≫ g = 0) :
    leftTensorMap 𝒪 f n ≫ map 𝒪 g (n + 1) = 0 := sorry

end SheafOfModules.RingedSite.SymmetricPower
