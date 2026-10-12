/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.ExtraDegeneracy
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.LastExtraDegeneracy
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Evaluation
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Extra degeneracies on evaluated comonad resolutions

A chosen section of the comonad counit supplies Mathlib's initial extra degeneracy on the
evaluated canonical resolution.  The core API therefore takes a `SplitEpi` for the counit; a
coalgebra is exposed only as a convenient source of that minimal datum.  In particular, the
coalgebra coassociativity law is not forced on downstream constructions that do not need it.

The same leaf transports either endpoint convention across the canonical augmented isomorphism
from an arbitrary realization, after applying any functor on augmented simplicial objects.
-/

@[expose] public section

open CategoryTheory.SimplicialObject
open Opposite
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe u v u' v'

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] {G : Comonad C}

namespace Realizes

/-- Transport an extra degeneracy from any functorial image of the canonical augmented comonad
resolution to the same image of an arbitrary realization. -/
@[stacks 08ND "extra degeneracy transported to a comonad realization"]
noncomputable def extraDegeneracy
    {D : Type u'} [Category.{v'} D] {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U)
    (F : SimplicialObject.Augmented (C ⥤ C) ⥤ SimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.ExtraDegeneracy
      (F.obj (simplicialResolution.augmented G))) :
    SimplicialObject.Augmented.ExtraDegeneracy (F.obj hU.augmented) :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso
    (Realizes.augmentedIso.map hU F).symm ed

/-- The zero-section of a transported extra degeneracy is conjugated by the point and
simplicial components of the mapped realization isomorphism. -/
@[simp, stacks 08ND "zero-section transported to a comonad realization"]
theorem extraDegeneracy.s'
    {D : Type u'} [Category.{v'} D] {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U)
    (F : SimplicialObject.Augmented (C ⥤ C) ⥤ SimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.ExtraDegeneracy
      (F.obj (simplicialResolution.augmented G))) :
    (Realizes.extraDegeneracy hU F ed).s' =
      (SimplicialObject.Augmented.point.mapIso
        (Realizes.augmentedIso.map hU F).symm).inv ≫ ed.s' ≫
      (SimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).hom.app (op ⦋0⦌) := sorry

/-- Each map of a transported extra degeneracy is conjugated by the corresponding degree
components of the mapped realization isomorphism. -/
@[simp, stacks 08ND "extra-degeneracy maps transported to a comonad realization"]
theorem extraDegeneracy.s
    {D : Type u'} [Category.{v'} D] {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U)
    (F : SimplicialObject.Augmented (C ⥤ C) ⥤ SimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.ExtraDegeneracy
      (F.obj (simplicialResolution.augmented G))) (n : ℕ) :
    (Realizes.extraDegeneracy hU F ed).s n =
      (SimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).inv.app (op ⦋n⦌) ≫ ed.s n ≫
      (SimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).hom.app (op ⦋n + 1⦌) := sorry

/-- Transport a last extra degeneracy from any functorial image of the canonical augmented
comonad resolution to the same image of an arbitrary realization. -/
@[stacks 08ND "last extra degeneracy transported to a comonad realization"]
noncomputable def lastExtraDegeneracy
    {D : Type u'} [Category.{v'} D] {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U)
    (F : SimplicialObject.Augmented (C ⥤ C) ⥤ SimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.LastExtraDegeneracy
      (F.obj (simplicialResolution.augmented G))) :
    SimplicialObject.Augmented.LastExtraDegeneracy (F.obj hU.augmented) :=
  SimplicialObject.Augmented.LastExtraDegeneracy.ofIso
    (Realizes.augmentedIso.map hU F).symm ed

/-- The zero-section of a transported last extra degeneracy is conjugated by the point and
simplicial components of the mapped realization isomorphism. -/
@[simp, stacks 08ND "last zero-section transported to a comonad realization"]
theorem lastExtraDegeneracy.s'
    {D : Type u'} [Category.{v'} D] {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U)
    (F : SimplicialObject.Augmented (C ⥤ C) ⥤ SimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.LastExtraDegeneracy
      (F.obj (simplicialResolution.augmented G))) :
    (Realizes.lastExtraDegeneracy hU F ed).s' =
      (SimplicialObject.Augmented.point.mapIso
        (Realizes.augmentedIso.map hU F).symm).inv ≫ ed.s' ≫
      (SimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).hom.app (op ⦋0⦌) := sorry

/-- Each map of a transported last extra degeneracy is conjugated by the corresponding degree
components of the mapped realization isomorphism. -/
@[simp, stacks 08ND "last-extra-degeneracy maps transported to a comonad realization"]
theorem lastExtraDegeneracy.s
    {D : Type u'} [Category.{v'} D] {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U)
    (F : SimplicialObject.Augmented (C ⥤ C) ⥤ SimplicialObject.Augmented D)
    (ed : SimplicialObject.Augmented.LastExtraDegeneracy
      (F.obj (simplicialResolution.augmented G))) (n : ℕ) :
    (Realizes.lastExtraDegeneracy hU F ed).s n =
      (SimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).inv.app (op ⦋n⦌) ≫ ed.s n ≫
      (SimplicialObject.Augmented.drop.mapIso
        (Realizes.augmentedIso.map hU F).symm).hom.app (op ⦋n + 1⦌) := sorry

end Realizes

namespace Coalgebra

/-- The structure map of a coalgebra exhibits the comonad counit at its underlying object as a
split epimorphism. -/
@[stacks 08ND "coalgebra splitting of a comonad counit"]
def counitSplitEpi (A : Coalgebra G) : SplitEpi (G.ε.app A.A) where
  section_ := A.a
  id := A.counit

/-- The chosen section in the counit splitting of a coalgebra is its structure map. -/
@[simp, stacks 08ND "section of the coalgebra counit splitting"]
theorem counitSplitEpi.section (A : Coalgebra G) : A.counitSplitEpi.section_ = A.a := sorry

end Coalgebra

namespace simplicialResolution.eval

namespace splitCounit

variable {X : C} (h : SplitEpi (G.ε.app X))

/-- The clean degreewise map underlying the extra degeneracy from a split counit.  This owner is
stated directly on positive iterates, independently of the bundled evaluated resolution. -/
@[stacks 08ND "iterated section from a split comonad counit"]
def iteratedSection (n : ℕ) :
    (G.toFunctor ⁺⦋n⦌).obj X ⟶ (G.toFunctor ⁺⦋n + 1⦌).obj X :=
  (G.toFunctor ⁺⦋n⦌).map h.section_ ≫
    (IteratedEndofunctor.prependIso G.toFunctor n).hom.app X

/-- The degree-zero section of the evaluated comonad resolution supplied by a split counit. -/
@[stacks 08ND "split-counit section of a comonad resolution"]
noncomputable def zeroSection :
    ((simplicialResolution.eval G).obj X).right ⟶
      ((simplicialResolution.eval G).obj X).left _⦋0⦌ :=
  h.section_

/-- In degree `n`, a split counit supplies the extra degeneracy obtained by applying the positive
iterate to its chosen section and reassociating the resulting iterate. -/
@[stacks 08ND "split-counit extra degeneracy of a comonad resolution"]
noncomputable def degeneracy (n : ℕ) :
    ((simplicialResolution.eval G).obj X).left _⦋n⦌ ⟶
      ((simplicialResolution.eval G).obj X).left _⦋n + 1⦌ :=
  iteratedSection h n

/-- The evaluated extra-degeneracy map is the clean iterated-section map on the underlying
positive iterates. -/
@[simp, stacks 08ND "evaluated split-counit degeneracy formula"]
theorem degeneracy_eq_iteratedSection (n : ℕ) : degeneracy h n = iteratedSection h n := sorry

/-- The split-counit section splits the resolution augmentation in degree zero. -/
@[stacks 08ND "split-counit section and resolution augmentation"]
theorem s'_comp_ε :
    zeroSection h ≫ ((simplicialResolution.eval G).obj X).hom.app (op ⦋0⦌) = 𝟙 _ := sorry

/-- The first split-counit extra degeneracy followed by the last face factors through the
augmentation and its section. -/
@[stacks 08ND "initial split-counit extra-degeneracy relation"]
theorem s₀_comp_δ₁ :
    degeneracy h 0 ≫ ((simplicialResolution.eval G).obj X).left.δ 1 =
      ((simplicialResolution.eval G).obj X).hom.app (op ⦋0⦌) ≫ zeroSection h := sorry

/-- Every split-counit extra degeneracy is a section of the zeroth face. -/
@[stacks 08ND "split-counit extra degeneracy and zeroth face"]
theorem s_comp_δ₀ (n : ℕ) :
    degeneracy h n ≫ ((simplicialResolution.eval G).obj X).left.δ 0 = 𝟙 _ := sorry

/-- Split-counit extra degeneracies commute with all remaining faces. -/
@[stacks 08ND "split-counit extra degeneracy and faces"]
theorem s_comp_δ (n : ℕ) (i : Fin (n + 2)) :
    degeneracy h (n + 1) ≫
        ((simplicialResolution.eval G).obj X).left.δ i.succ =
      ((simplicialResolution.eval G).obj X).left.δ i ≫ degeneracy h n := sorry

/-- Split-counit extra degeneracies commute with the ordinary degeneracies. -/
@[stacks 08ND "split-counit extra degeneracy and degeneracies"]
theorem s_comp_σ (n : ℕ) (i : Fin (n + 1)) :
    degeneracy h n ≫ ((simplicialResolution.eval G).obj X).left.σ i.succ =
      ((simplicialResolution.eval G).obj X).left.σ i ≫ degeneracy h (n + 1) := sorry

/-- A split comonad counit equips the evaluated canonical resolution with an extra degeneracy. -/
@[stacks 08ND "extra degeneracy from a split comonad counit"]
noncomputable def extraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy
      ((simplicialResolution.eval G).obj X) where
  s' := zeroSection h
  s := degeneracy h
  s'_comp_ε := s'_comp_ε h
  s₀_comp_δ₁ := s₀_comp_δ₁ h
  s_comp_δ₀ := s_comp_δ₀ h
  s_comp_δ := s_comp_δ h
  s_comp_σ := s_comp_σ h

/-- The section stored by the split-counit extra degeneracy is the chosen counit section. -/
@[simp, stacks 08ND "section of the split-counit extra degeneracy"]
theorem extraDegeneracy.s' : (extraDegeneracy h).s' = h.section_ := sorry

/-- The degreewise maps stored by the split-counit extra degeneracy are the iterated chosen
section maps. -/
@[simp, stacks 08ND "maps of the split-counit extra degeneracy"]
theorem extraDegeneracy.s (n : ℕ) : (extraDegeneracy h).s n = degeneracy h n := sorry

end splitCounit

/-- A comonad coalgebra supplies the canonical extra degeneracy on the resolution of its
underlying object. -/
@[stacks 08ND "extra degeneracy on a coalgebra resolution"]
noncomputable def extraDegeneracy (A : Coalgebra G) :
    SimplicialObject.Augmented.ExtraDegeneracy
      ((simplicialResolution.eval G).obj A.A) :=
  splitCounit.extraDegeneracy A.counitSplitEpi

/-- The coalgebra extra degeneracy is obtained solely from the coalgebra's split counit. -/
@[stacks 08ND "coalgebra extra degeneracy as a split-counit construction"]
theorem extraDegeneracy.eq_splitCounit (A : Coalgebra G) :
    extraDegeneracy A = splitCounit.extraDegeneracy A.counitSplitEpi := sorry

/-- The section stored by the coalgebra extra degeneracy is the coalgebra structure map. -/
@[simp, stacks 08ND "section of the coalgebra extra degeneracy"]
theorem extraDegeneracy.s' (A : Coalgebra G) : (extraDegeneracy A).s' = A.a := sorry

/-- The degreewise maps stored by the coalgebra extra degeneracy apply a positive iterate to the
coalgebra structure map. -/
@[simp, stacks 08ND "maps of the coalgebra extra degeneracy"]
theorem extraDegeneracy.s (A : Coalgebra G) (n : ℕ) :
    (extraDegeneracy A).s n =
      (G.toFunctor ⁺⦋n⦌).map A.a ≫
        (IteratedEndofunctor.prependIso G.toFunctor n).hom.app A.A := sorry

end simplicialResolution.eval

end CategoryTheory.Comonad
