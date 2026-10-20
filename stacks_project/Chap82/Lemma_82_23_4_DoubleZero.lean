/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap82.Remark_82_22_3_Pullback

/-!
# Interchange of iterated zero schemes

The two presentations of `D ∩ D'` as iterated zero schemes of sections of
invertible modules are canonically isomorphic by a functor-of-points swap.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DoubleZero

/-- The iterated zero scheme `Z(s'|_{Z(s)})` of a restricted section. -/
noncomputable abbrev iterate {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')] :
    ClosedSubspace (zeroScheme L s).X :=
  zeroScheme ((Modules.pullback (zeroSchemeι L s)).obj L')
    (Modules.sectionsPullback (zeroSchemeι L s) L' s')

/-- Unfolding of the iterated zero scheme as the zero scheme of the restricted
section. -/
theorem iterate_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')] :
    iterate L L' s s' =
      zeroScheme ((Modules.pullback (zeroSchemeι L s)).obj L')
        (Modules.sectionsPullback (zeroSchemeι L s) L' s') :=
  sorry

/-- A `T`-point of `Z(s|_{Z(s')})` maps to a `T`-point of `Z(s)` along which the
restricted section `s'` vanishes. -/
theorem swapHom_vanishes {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)]
    {T : (Over S)ᵒᵖ} (p : (iterate L' L s' s).X.functorOfPoints.obj T) :
    vanishes
      (homOfPoint ((zeroSchemePullbackMap (zeroSchemeι L' s') L s).app T p))
      (zeroIdealSubobject ((Modules.pullback (zeroSchemeι L s)).obj L')
        (Modules.sectionsPullback (zeroSchemeι L s) L' s')) :=
  sorry

/-- The canonical morphism `Z(s|_{Z(s')}) ⟶ Z(s'|_{Z(s)})` on functor of points. -/
noncomputable def swapHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)] :
    (iterate L' L s' s).X ⟶ (iterate L L' s s').X where
  app T :=
    TypeCat.ofHom fun (p : (iterate L' L s' s).X.functorOfPoints.obj T) ↦
      (⟨(zeroSchemePullbackMap (zeroSchemeι L' s') L s).app T p,
          swapHom_vanishes L L' s s' p⟩ :
        (iterate L L' s s').X.functorOfPoints.obj T)
  naturality := sorry

/-- The swap morphism composed with the immersion of `Z(s'|_{Z(s)})` recovers the
canonical map to `Z(s)`. -/
theorem swapHom_comp_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)] :
    swapHom L L' s s' ≫ (iterate L L' s s').ι =
      zeroSchemePullbackMap (zeroSchemeι L' s') L s :=
  sorry

/-- The canonical isomorphism `Z(s|_{Z(s')}) ≅ Z(s'|_{Z(s)})` exchanging the order
of vanishing. -/
noncomputable def swapIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)] :
    (iterate L' L s' s).X ≅ (iterate L L' s s').X where
  hom := swapHom L L' s s'
  inv := swapHom L' L s' s
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The interchange isomorphism composed with the immersion of `Z(s'|_{Z(s)})`
recovers the canonical map to `Z(s)`. -/
theorem swapIso_hom_fst {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)] :
    (swapIso L L' s s').hom ≫ (iterate L L' s s').ι =
      zeroSchemePullbackMap (zeroSchemeι L' s') L s :=
  sorry

/-- The interchange isomorphism composed with the canonical map to `Z(s')`
recovers the immersion of `Z(s|_{Z(s')})`. -/
theorem swapIso_hom_snd {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)] :
    (swapIso L L' s s').hom ≫
        zeroSchemePullbackMap (zeroSchemeι L s) L' s' =
      (iterate L' L s' s).ι :=
  sorry

/-- The interchange of iterated zero schemes respects structure morphisms to a
common base. -/
theorem swapIso_hom_comp_structure {S : Scheme.{u}}
    {B X : AlgebraicSpace S} (f : X ⟶ B)
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)] :
    (swapIso L L' s s').hom ≫
        ((iterate L L' s s').ι ≫ zeroSchemeι L s ≫ f) =
      (iterate L' L s' s).ι ≫ zeroSchemeι L' s' ≫ f :=
  sorry

/-- The interchange morphism of iterated zero schemes is proper. -/
instance instProper_swapIso_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L L' : X.Modules) [isInvertibleObject L] [isInvertibleObject L']
    (s : L.sections) (s' : L'.sections)
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L s)).obj L')]
    [isInvertibleObject ((Modules.pullback (zeroSchemeι L' s')).obj L)] :
    Proper (swapIso L L' s s').hom :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace.DoubleZero
