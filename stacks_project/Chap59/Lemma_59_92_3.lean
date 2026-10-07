module

public import stacks_project.Chap59.Lemma_59_92_3_BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 59.92.3: if `f : X ⟶ Y` is a proper morphism of schemes, `g : Y' ⟶ Y` is
any morphism of schemes, `X' = Y' ×_Y X` with projections `f'` and `g'`, `n ≥ 1`,
and `E ∈ D(X_étale, ZMod n)`, then the base-change map (59.91.5.2)
`zmodDerivedBaseChangeHom` `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism. -/
@[stacks 0F0C]
theorem zmodDerivedBaseChangeHom_isIso_of_isProper
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ) [NeZero n]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso (zmodDerivedBaseChangeHom f g f' g' h_cart n E) := sorry

/-- Specialization of `zmodDerivedBaseChangeHom_isIso_of_isProper` to the chosen
fibre product `Y' ×_Y X`, with projections `f' = pullback.fst g f` and
`g' = pullback.snd g f`. -/
theorem zmodDerivedBaseChangeHom_isIso_of_isProper_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y)
    [HasPullback g f] (n : ℕ) [NeZero n]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf (pullback g f).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso
      (zmodDerivedBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip n E) := sorry

end AlgebraicGeometry.Scheme.Etale

end

end
