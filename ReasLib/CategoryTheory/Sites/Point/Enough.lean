/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.FiniteRefinement
public import ReasLib.CategoryTheory.Sites.Point.SeparatingSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Enough points and indexed point families

This module supplies the indexed-family interface to the canonical
`GrothendieckTopology.HasEnoughPoints` and
`ObjectProperty.IsConservativeFamilyOfPoints` owners.  It also records the
stalkwise tests and the cover-local criterion that are useful when constructing
enough points on a site.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w w' w''

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace PointFamily

/-- An indexed family of points is conservative precisely when its stalk functors jointly
reflect isomorphisms. -/
theorem isConservative_iff
    {ι : Type w'} (p : ι → Point.{w} J) :
    (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints ↔
      ∀ ⦃F G : Sheaf J (Type w)⦄ (f : F ⟶ G),
        (∀ i : ι, IsIso ((p i).sheafFiber.map f)) → IsIso f := sorry

/-- The stalk functors of an indexed conservative family jointly reflect isomorphisms. -/
theorem jointlyReflectsIsomorphisms
    {ι : Type w'} (p : ι → Point.{w} J)
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints) :
    JointlyReflectIsomorphisms
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type w) ⥤ Type w)) := sorry

section Stalkwise

variable [LocallySmall.{w} C]
variable {ι : Type w'} (p : ι → Point.{w} J)
variable {F G : Sheaf J (Type w)}

/-- Stalkwise injectivity along a conservative indexed family implies that a sheaf map is mono. -/
theorem mono_of_stalkwise_injective
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (f : F ⟶ G)
    (hf : ∀ i : ι, Function.Injective ((p i).sheafFiber.map f)) :
    Mono f := sorry

/-- Stalkwise surjectivity along a conservative indexed family implies that a sheaf map is epi. -/
theorem epi_of_stalkwise_surjective
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (f : F ⟶ G)
    (hf : ∀ i : ι, Function.Surjective ((p i).sheafFiber.map f)) :
    Epi f := sorry

/-- Maps of sheaves are equal when they agree after applying every stalk functor in a conservative
indexed family. -/
theorem hom_ext_of_stalkwise
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    {f g : F ⟶ G}
    (hfg : ∀ i : ι, (p i).sheafFiber.map f = (p i).sheafFiber.map g) :
    f = g := sorry

variable {K : Type w''} [Category K] [FinCategory K]
variable {D : K ⥤ Sheaf J (Type w)}

/-- A cone on a finite sheaf diagram is limiting exactly when all stalkwise cones for a
conservative indexed family are limiting. -/
theorem isLimit_iff_stalkwise
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (c : Cone D) :
    Nonempty (IsLimit c) ↔
      ∀ i : ι, Nonempty (IsLimit ((p i).sheafFiber.mapCone c)) := sorry

/-- A cocone on a finite sheaf diagram is colimiting exactly when all stalkwise cocones for a
conservative indexed family are colimiting. -/
theorem isColimit_iff_stalkwise
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (c : Cocone D) :
    Nonempty (IsColimit c) ↔
      ∀ i : ι, Nonempty (IsColimit ((p i).sheafFiber.mapCocone c)) := sorry

end Stalkwise

section Exactness

variable [LocallySmall C]

/-- Lemma 18.14.4 (1): a conservative indexed family of points detects exact short complexes
of abelian sheaves stalkwise. -/
@[stacks 05V3 "conservative family"]
theorem exact_iff_stalkwise
    {I : Type w'} (p : I → J.Point)
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    S.Exact ↔ ∀ i : I, (S.map (p i).sheafFiber).Exact := sorry

end Exactness

/-- An indexed family of points is conservative exactly when its germs distinguish unequal local
sections of every set-valued sheaf. -/
theorem isConservative_iff_separatingSections
    {ι : Type w'} (p : ι → Point.{w} J)
    [LocallySmall.{w} C] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)] :
    (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints ↔
      ∀ ⦃F : Sheaf J (Type w)⦄ (U : C) (s t : F.obj.obj (Opposite.op U)),
        s ≠ t →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x F.obj s ≠ (p i).toPresheafFiber U x F.obj t := sorry

end PointFamily

namespace HasEnoughPoints

section Stalkwise

variable [LocallySmall C]

/-- Lemma 18.14.4 (2): on a site with enough points, exactness of a short complex of abelian
sheaves is equivalent to exactness on every stalk. -/
@[stacks 05V3 "enough points"]
theorem exact_iff_stalkwise
    [HasEnoughPoints.{max u v} J]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    S.Exact ↔ ∀ p : J.Point, (S.map p.sheafFiber).Exact := sorry

end Stalkwise

/-- A site has enough points exactly when it admits a small indexed conservative family of points. -/
theorem iff_exists_indexedConservativeFamily :
    HasEnoughPoints.{w} J ↔
      ∃ (ι : Type w) (p : ι → Point.{w} J),
        (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := sorry

/-- Extract a small indexed conservative family from an enough-points hypothesis. -/
theorem exists_indexedConservativeFamily
    (hJ : HasEnoughPoints.{w} J) :
    ∃ (ι : Type w) (p : ι → Point.{w} J),
      (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := sorry

/-- A small indexed conservative family supplies enough points on its ambient site. -/
theorem of_indexedConservativeFamily
    {ι : Type w} (p : ι → Point.{w} J)
    (hP : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints) :
    HasEnoughPoints.{w} J := sorry

/-- A covering family whose slice sites all have enough points supplies enough points on the
ambient site. -/
theorem of_coversTop
    [LocallySmall.{w} C]
    {ι : Type w} (U : ι → C) (hU : J.CoversTop U)
    (hlocal : ∀ i : ι, HasEnoughPoints.{w} (J.over (U i))) :
    HasEnoughPoints.{w} J := sorry

/-- A covering family whose slice sites have finite limits and finite refinements has enough
points on the ambient site. -/
theorem of_coversTop_of_slice_finiteRefinement
    [LocallySmall.{max (u + 1) (v + 1)} C]
    {ι : Type (max (u + 1) (v + 1))} (U : ι → C) (hU : J.CoversTop U)
    [∀ i : ι, HasFiniteLimits (Over (U i))]
    (hfinite : ∀ i : ι, ∀ X : Over (U i),
      (J.over (U i)).HasFiniteRefinement X) :
    HasEnoughPoints.{max (u + 1) (v + 1)} J := sorry

end HasEnoughPoints

end CategoryTheory.GrothendieckTopology
