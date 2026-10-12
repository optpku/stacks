/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
public import stacks_project.Chap75.Lemma_75_13_3_Pullback

/-!
# Internal-Hom comparison along ε*

The morphism ε of 75.4.0.1 is the commutative small Zariski-to-étale restriction
`commSmallEtaleToZariski`. Exact derived pullback along this flat morphism
carries the canonical lax-monoidal internal-Hom comparison from
`Functor.LaxMonoidal.InternalHom`.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open CategoryTheory.MonoidalClosed
open Functor.LaxMonoidal
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

variable (X : Scheme.{u})
variable [MonoidalCategory (ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))]
variable [MonoidalClosed (ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))]
variable [MonoidalCategory (ModuleDerived.{u + 1} (smallCommRingedSite .etale X))]
variable [MonoidalClosed (ModuleDerived.{u + 1} (smallCommRingedSite .etale X))]
variable [(commSmallEtaleToZariskiDerived X).LaxMonoidal]

/-- The canonical comparison `ε* (ihom E).obj F ⟶ (ihom (ε* E)).obj (ε* F)` along
exact derived pullback `commSmallEtaleToZariskiDerived`. -/
noncomputable abbrev comparison
    (E F : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    (commSmallEtaleToZariskiDerived X).obj ((ihom E).obj F) ⟶
      (ihom ((commSmallEtaleToZariskiDerived X).obj E)).obj
        ((commSmallEtaleToZariskiDerived X).obj F) :=
  InternalHom.comparison (commSmallEtaleToZariskiDerived X) E F

end AlgebraicGeometry.Scheme.SiteRestriction
