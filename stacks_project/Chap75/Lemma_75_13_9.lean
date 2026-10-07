module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import stacks_project.Chap75.Lemma_75_13_9_Comparison

/-!
# Lemma 75.13.9

The canonical internal-Hom comparison along exact derived pullback of ε from
75.4.0.1 is an isomorphism when the source is pseudo-coherent and the target
lies in D⁺, or when the source is perfect.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open DerivedCategory.TStructure
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

variable {X : Scheme.{u}}
variable [MonoidalCategory (ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))]
variable [MonoidalClosed (ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))]
variable [MonoidalCategory (ModuleDerived.{u + 1} (smallCommRingedSite .etale X))]
variable [MonoidalClosed (ModuleDerived.{u + 1} (smallCommRingedSite .etale X))]
variable [(commSmallEtaleToZariskiDerived X).LaxMonoidal]
variable {E F : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)}

/-- Lemma 75.13.9 (1): for a scheme `X` and objects `E`, `F` of `D(𝒪_X)`, if `E`
is pseudo-coherent and `F` lies in `D⁺(𝒪_X)`, then the canonical comparison
`ε* (ihom E).obj F ⟶ (ihom (ε* E)).obj (ε* F)` along
`commSmallEtaleToZariskiDerived` is an isomorphism. -/
@[stacks 08JP]
theorem isIso_of_isPseudoCoherent (hE : E.IsPseudoCoherent)
    (hF : (t.plus : ObjectProperty _) F) :
    IsIso (comparison X E F) := sorry

/-- Lemma 75.13.9 (2): for a scheme `X` and objects `E`, `F` of `D(𝒪_X)`, if `E`
is perfect, then the canonical comparison
`ε* (ihom E).obj F ⟶ (ihom (ε* E)).obj (ε* F)` along
`commSmallEtaleToZariskiDerived` is an isomorphism. -/
@[stacks 08JP]
theorem isIso_of_isPerfect (hE : E.IsPerfect) :
    IsIso (comparison X E F) := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
