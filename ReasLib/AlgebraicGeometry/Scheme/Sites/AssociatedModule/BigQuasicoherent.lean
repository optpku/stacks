/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Quasicoherent modules on big standard sites

This module records closure properties of quasicoherent module sheaves on the
big standard sites of a scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent

/-- Quasicoherent modules on a big standard site are closed under colimits of
every universe-compatible shape. -/
@[instance]
theorem closedUnderColimitsOfShape (S : Scheme.{u}) (τ : StandardTopology)
    (J : Type v) [Category.{w} J] :
    IsClosedUnderColimitsOfShape
      (SheafOfModules.isQuasicoherent (bigStructureSheaf τ S)) J := sorry

/-- A coproduct of quasicoherent modules on a big standard site is
quasicoherent. -/
@[instance]
theorem coproduct (S : Scheme.{u}) (τ : StandardTopology) {ι : Type v}
    (F : ι → SheafOfModules (bigStructureSheaf τ S))
    [HasCoproduct F] [∀ i, (F i).IsQuasicoherent] :
    (∐ F).IsQuasicoherent := sorry

/-- Quasicoherent modules on a big standard site are closed under
cokernels. -/
@[instance]
theorem closedUnderCokernels (S : Scheme.{u}) (τ : StandardTopology) :
    (SheafOfModules.isQuasicoherent
      (bigStructureSheaf τ S)).IsClosedUnderCokernels := sorry

/-- Quasicoherent modules on a big standard site are closed under
extensions. -/
@[instance]
theorem closedUnderExtensions (S : Scheme.{u}) (τ : StandardTopology) :
    (SheafOfModules.isQuasicoherent
      (bigStructureSheaf τ S)).IsClosedUnderExtensions := sorry

/-- Internal Hom from a finite locally free module to a quasicoherent module
on a big standard site is quasicoherent. -/
@[instance]
theorem internalHom (S : Scheme.{u}) (τ : StandardTopology)
    (F G : RingedSite.ModuleCat.{u + 1} (bigCommRingedSite τ S))
    [F.IsFiniteLocallyFree] [G.IsQuasicoherent] :
    ((ihom F).obj G).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent
