/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Successive
import StacksCheckRecall

/-!
# Lifting a complex of modules along a surjection of ring sheaves

On a site, a locally surjective map of ring sheaves, a termwise-flat successive family of
𝒪-modules vanishing in high degree, and maps to a homology-bounded complex of 𝒪₀-modules
that induce a chain map after extension of scalars, lift to a termwise-flat successive
family whose extension is a quasi-isomorphic complex.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.Successive

/- Lemma 91.16.1: Let `C` be a site and `π : 𝒪 ⟶ 𝒪₀` a surjection of sheaves of rings.
Given a termwise-flat successive family `G` of `𝒪`-modules with `G.X n = 0` for `n ≫ 0`,
a complex `K₀` of `𝒪₀`-modules with `Hⁿ(K₀) = 0` for `n ≫ 0`, and maps of `𝒪`-modules
`G.X n ⟶ (restrictionAlong π).obj (K₀.X n)` inducing a complex `G ⊗_𝒪 𝒪₀` and a chain
map to `K₀`, there exist a termwise-flat successive family `F` of `𝒪`-modules vanishing
for `n ≫ 0`, a morphism `G ⟶ F` of successive objects, and maps
`F.X n ⟶ (restrictionAlong π).obj (K₀.X n)` recovering the given maps by composition,
such that `F ⊗_𝒪 𝒪₀` is a complex and the induced map `F ⊗_𝒪 𝒪₀ ⟶ K₀` is a
quasi-isomorphism. -/
@[stacks 0DIT]
#check (SheafOfModules.RingedSite.Successive.existsFlatLift :
  ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {𝒪 𝒪₀ : Sheaf J CommRingCat.{u}} (π : 𝒪 ⟶ 𝒪₀) [Sheaf.IsLocallySurjective π]
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (hGflat : IsTermwiseFlat G) (hGzero : ∃ N, G.IsStrictlyLE N)
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (hK : ∃ N, K₀.IsLE N)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n))
    (hφ : IsChainMapAfterExtend π G K₀ φ),
    ∃ (F : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
      (ι : CategoryTheory.Successive.Hom G F)
      (ψ : ∀ n, F.X n ⟶ (restrictionAlong π).obj (K₀.X n))
      (hψ : IsChainMapAfterExtend π F K₀ ψ),
      IsTermwiseFlat F ∧
        (∃ N, F.IsStrictlyLE N) ∧
        (∀ n, ι.f n ≫ ψ n = φ n) ∧
        QuasiIso (homAfterExtend π F K₀ ψ hψ))

end SheafOfModules.RingedSite.Successive
