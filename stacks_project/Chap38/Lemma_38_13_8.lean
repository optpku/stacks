/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locus.WeaklyAssociated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 38.13.8 (1): for a locally finite-type morphism `f : X ⟶ S`, the locus where
`f` is flat is open when the weakly associated points of `S` form a locally finite family. -/
@[stacks 05IM]
#check
  (AlgebraicGeometry.Scheme.Hom.isOpen_flatAt_of_locallyFinite_weakAss :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
      LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S)) →
        IsOpen {x : X | AlgebraicGeometry.Scheme.Hom.flatAt f x})

#check
  (AlgebraicGeometry.Scheme.Hom.flatLocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
      LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S)) → X.Opens)

#check
  (AlgebraicGeometry.Scheme.Hom.mem_flatLocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) (x : X),
      x ∈ AlgebraicGeometry.Scheme.Hom.flatLocus f h_weakAss ↔
        AlgebraicGeometry.Scheme.Hom.flatAt f x)

/- Lemma 38.13.8 (2): the restriction of `f` to its flat locus is flat. -/
@[stacks 05IM]
#check
  (AlgebraicGeometry.Scheme.Hom.flatLocus_isFlat :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
      Flat ((AlgebraicGeometry.Scheme.Hom.flatLocus f h_weakAss).ι ≫ f))

/- Lemma 38.13.8 (3): the restriction of `f` to its flat locus is locally of finite
presentation. -/
@[stacks 05IM]
#check
  (AlgebraicGeometry.Scheme.Hom.flatLocus_isLocallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
      LocallyOfFinitePresentation
        ((AlgebraicGeometry.Scheme.Hom.flatLocus f h_weakAss).ι ≫ f))

end AlgebraicGeometry
