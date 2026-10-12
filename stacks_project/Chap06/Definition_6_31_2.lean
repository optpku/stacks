/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.OpenSubsetExtensionByInitial
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

/-
The source uses one restriction notation for four related constructions. Mathlib's canonical
owners keep their coefficient hypotheses and functorial structure visible: presheaf and sheaf
restriction are `TopCat.Presheaf.pullback` and `TopCat.Sheaf.pullback`, module restriction is
`PresheafOfModules.pullback` applied to the adjunction unit, and the associated open ringed
subspace is `SheafedSpace.restrict`. Direct tagged recalls/checks avoid a partial local notation
that covered only sheaves while preserving the exact open-inclusion specializations below.
-/

/- Definition 6.31.2 (1): restriction of a presheaf is pullback along the open inclusion. -/
@[stacks 00A1 "presheaf restriction along an open inclusion"]
recall TopCat.Presheaf.pullback

/- Definition 6.31.2 (2): restriction of a sheaf is pullback along the open inclusion. -/
@[stacks 00A1 "sheaf restriction along an open inclusion"]
recall TopCat.Sheaf.pullback

/- Definition 6.31.2 (3): the open subspace of a ringed space associated to an open subset is
the restriction of its structure sheaf along the open embedding. -/
@[stacks 00A1 "open subspace of a ringed space"]
#check fun (X : RingedSpace.{u}) (U : Opens X.carrier) ↦ X.restrict U.isOpenEmbedding

section ModuleRestriction

variable {X : TopCat.{u}} (U : Opens X) (𝒪 : X.Presheaf CommRingCat.{u})

/- Definition 6.31.2 (4): restriction of a presheaf of `𝒪`-modules to `U` is the canonical
module pullback induced by the commutative-ring pullback-pushforward unit. The shared
`CommRing.restriction` API records the restricted scalar presheaf without exposing a separate
multiplication-map wrapper. -/
@[stacks 00A1 "restriction of a presheaf of modules"]
#check
  (PresheafOfModules.OpenSubset.ExtensionByZero.CommRing.restriction U 𝒪 :
    PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm 𝒪) ⥤
      PresheafOfModules
        (CategoryTheory.Presheaf.ringPresheafOfComm
          ((TopCat.Presheaf.pullback CommRingCat.{u} U.inclusion').obj 𝒪)))

end ModuleRestriction

end
