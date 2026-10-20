/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Stability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Openness
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FiniteSeparableCoproduct
public import ReasLib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.RingTheory.RingHom.Etale.StandardSmooth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Proposition 59.26.2 (1): a scheme over a field is étale exactly when it is a disjoint union
of spectra of finite separable field extensions. -/
@[stacks 03PC] #check
  (AlgebraicGeometry.etale_iff_schemeAsDisjointUnionOfSpecFiniteSeparable :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k),
      Etale X.hom ↔
        Nonempty (SchemeAsDisjointUnionOfSpecFiniteSeparable k X))

/- Proposition 59.26.2 (2): étaleness is equivalent to local finite presentation, flatness, and
finite-separable étale fibres. -/
@[stacks 03PC] #check
  (AlgebraicGeometry.Etale.iff_locallyOfFinitePresentation_flat_etaleFibers :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Etale f ↔
        LocallyOfFinitePresentation f ∧ Flat f ∧
          (∀ s : S, Etale (f.fiberToSpecResidueField s)))

/- Proposition 59.26.2 (3): étaleness is also equivalent to flatness,
unramifiedness, and local finite presentation. -/
@[stacks 03PC] #check
  (AlgebraicGeometry.Etale.iff_flat_and_unramified_and_locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      Etale f ↔ Flat f ∧ Unramified f ∧ LocallyOfFinitePresentation f)

/- Proposition 59.26.2 (4): the ring-map Jacobian criterion for étaleness. -/
@[stacks 03PC] #check
  (RingHom.etale_iff_standardSmooth_zero :
    ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S),
      RingHom.Etale f ↔ RingHom.IsStandardSmoothOfRelativeDimension 0 f)

/- Proposition 59.26.2 (5): étale morphisms are stable under base change. -/
@[stacks 03PC] #check
  (@AlgebraicGeometry.Etale.of_isPullback :
    ∀ {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
      {i : Y' ⟶ X} {f' : Y' ⟶ Y},
      IsPullback i f' f g → Etale f → Etale f')

/- Proposition 59.26.2 (6): compositions of étale morphisms are étale. -/
@[stacks 03PC] #check
  (@AlgebraicGeometry.Etale.comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      Etale f → Etale g → Etale (f ≫ g))

/- Proposition 59.26.2 (7): pullbacks of étale morphisms remain étale. -/
@[stacks 03PC] #check
  (@AlgebraicGeometry.Etale.pullback_fst :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S),
      HasPullback f g → Etale g → Etale (pullback.fst f g))

/- Proposition 59.26.2 (8): products of étale morphisms are étale. -/
@[stacks 03PC] #check
  (CategoryTheory.MorphismProperty.IsStableUnderBaseChange.prod_map :
    ∀ {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : Y ⟶ Z),
      Etale f → Etale g → Etale (Limits.prod.map f g))

/- Proposition 59.26.2 (9): an étale morphism has relative dimension zero. -/
@[stacks 03PC] #check
  (AlgebraicGeometry.Scheme.Hom.etale_iff_smoothOfRelativeDimension_zero :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      Etale f ↔ SmoothOfRelativeDimension 0 f)

/- Proposition 59.26.2 (10): an étale morphism preserves reducedness. -/
@[stacks 03PC] #check
  (AlgebraicGeometry.Etale.isReduced :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsReduced X], IsReduced Y)

/- Proposition 59.26.2 (11): an étale morphism preserves regularity. -/
@[stacks 03PC] #check
  (AlgebraicGeometry.Etale.isRegular :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [Scheme.Regular X], Scheme.Regular Y)

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/- Proposition 59.26.2 (12): étale morphisms are open. -/
@[stacks 03PC] #check
  (@AlgebraicGeometry.Etale.isOpenMap :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Etale f → IsOpenMap f.base)

end

/- Proposition 59.26.2 (13): an S-morphism between schemes étale over S is étale. -/
@[stacks 03PC] #check
  (AlgebraicGeometry.etale_of_etale_over :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
      Etale X.hom → Etale Y.hom → Etale f.left)
