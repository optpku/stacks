module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Section.ConnectedComponent
import StacksCheckRecall

open CategoryTheory

universe u

/- Theorem 41.6.2 (1): A section of an unramified separated morphism to a connected
scheme is an open immersion whose range is a unique connected component on which the
morphism is an isomorphism. -/
@[stacks 024U]
#check
  (AlgebraicGeometry.Scheme.Hom.Section.isOpenImmersion_and_existsUnique_connectedComponent :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [ConnectedSpace Y]
      [AlgebraicGeometry.Unramified f] [AlgebraicGeometry.IsSeparated f]
      (s : SplitEpi f),
      AlgebraicGeometry.IsOpenImmersion s.section_ ∧
        ∃! C : ConnectedComponents X,
          Set.range s.section_ = C.set ∧
            ∃ U : X.Opens, (U : Set X) = C.set ∧ IsIso (U.ι ≫ f))

/- Theorem 41.6.2 (2): Evaluating sections at a point of the connected base injects them
into the connected components of the source, with image exactly the components whose open
subscheme maps isomorphically to the base. -/
@[stacks 024U]
#check
  (AlgebraicGeometry.Scheme.Hom.Section.componentAt_injective_and_range :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [ConnectedSpace Y]
      [AlgebraicGeometry.Unramified f] [AlgebraicGeometry.IsSeparated f] (y : Y),
      Function.Injective
          (fun s : SplitEpi f ↦ (s.section_ y : ConnectedComponents X)) ∧
        Set.range (fun s : SplitEpi f ↦ (s.section_ y : ConnectedComponents X)) =
          {C | ∃ U : X.Opens, (U : Set X) = C.set ∧ IsIso (U.ι ≫ f)})

/- Theorem 41.6.2 (3): At most one section of an unramified separated morphism to a
connected scheme passes through any given point of the source. -/
@[stacks 024U]
#check
  (AlgebraicGeometry.Scheme.Hom.Section.eq_of_mem_section_ranges :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [ConnectedSpace Y]
      [AlgebraicGeometry.Unramified f] [AlgebraicGeometry.IsSeparated f]
      (x : X) (s t : SplitEpi f),
      x ∈ Set.range s.section_ → x ∈ Set.range t.section_ → s = t)
