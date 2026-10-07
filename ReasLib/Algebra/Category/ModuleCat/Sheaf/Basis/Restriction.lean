module

public import ReasLib.Topology.Sheaves.Basis.Algebraic.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Basis.Extension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Restriction of module sheaves to a topological basis

This module supplies the canonical restriction functor for modules over a ring sheaf and its
equivalence property. The basis sheaf/site comparison itself remains owned by the existing
topological-basis infrastructure.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}}
variable {B : Set (Opens X)} (hB : Opens.IsBasis B)

namespace BasisSiteSheaf

/-- The canonical restriction functor from sheaves of `𝒪`-modules on `X` to sheaves of modules
over the restriction of `𝒪` to the basis `B`. -/
noncomputable abbrev moduleRestriction (𝒪 : TopCat.Sheaf RingCat.{u} X) :
    Mod(𝒪) ⥤ Mod(BasisSiteSheaf.restrict hB 𝒪) :=
  SheafOfModules.pushforward (𝟙 (BasisSiteSheaf.restrict hB 𝒪))

/-- Restriction to the members of a topological basis is an equivalence for sheaves of modules
over a possibly noncommutative ring sheaf. -/
instance moduleRestriction_isEquivalence
    (𝒪 : TopCat.Sheaf RingCat.{u} X) :
    (moduleRestriction hB 𝒪).IsEquivalence := sorry

/-- Restriction to a topological basis induces the canonical equivalence on morphisms of module
sheaves. -/
noncomputable def moduleRestrictionHomEquiv
    {𝒪 : TopCat.Sheaf RingCat.{u} X} (M N : SheafOfModules 𝒪) :
    (M ⟶ N) ≃
      ((moduleRestriction hB 𝒪).obj M ⟶ (moduleRestriction hB 𝒪).obj N) :=
  (Functor.FullyFaithful.ofFullyFaithful (moduleRestriction hB 𝒪)).homEquiv

end BasisSiteSheaf
