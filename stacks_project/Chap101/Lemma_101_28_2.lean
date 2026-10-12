/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import stacks_project.Chap101.Definition_101_28_1_Gerbe

/-!
# Sheafification of isomorphism classes of a gerbe

If an algebraic stack is a gerbe over an algebraic space, the fppf sheafification
of its presheaf of fiberwise isomorphism classes is identified with that space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open FiberedCategoryOver FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The fppf sheafification of the presheaf sending a scheme `U` over `S` to the
isomorphism classes of objects in the fiber of an algebraic stack `X` over `U`. -/
noncomputable def isoClassSheaf {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (Scheme.fppfTopology.over S).sheafify (Functor.fiberIsoClassPresheaf X.p)

/-- `isoClassSheaf X` is the fppf sheafification of
`Functor.fiberIsoClassPresheaf X.p`. -/
theorem isoClassSheaf_spec {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    isoClassSheaf X =
      (Scheme.fppfTopology.over S).sheafify (Functor.fiberIsoClassPresheaf X.p) :=
  sorry

/-- The sheafification `isoClassSheaf X` is an fppf sheaf on `Over S`. -/
theorem isoClassSheaf_isSheaf {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (isoClassSheaf X) :=
  sorry

/-- Universe-raised functor of points of an algebraic space, as an fppf sheaf. -/
theorem functorOfPoints_ulift_isSheaf {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- Comparison from fiberwise isomorphism classes of an algebraic space to its
universe-raised functor of points, by Grothendieck fiber evaluation. -/
noncomputable def isoClassToPoints {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    Functor.fiberIsoClassPresheaf Y.toGroupoids.p ⟶
      Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u} where
  app U :=
    TypeCat.ofHom
      (Quotient.lift
        (fun x : Y.toGroupoids.p.Fiber (unop U) ↦
          ULift.up.{u + 1, u}
            (Sets.ofPresheaf.fiberToValue Y.functorOfPoints
              (unop U) x))
        sorry :
        (Functor.fiberIsoClassPresheaf Y.toGroupoids.p).obj U →
          (Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u}).obj U)
  naturality := sorry

/-- On a represented fiber class, `isoClassToPoints` is universe-lifted Grothendieck
fiber evaluation. -/
theorem isoClassToPoints_app_mk {S : Scheme.{u}} (Y : AlgebraicSpace S)
    (U : (Over S)ᵒᵖ) (x : Y.toGroupoids.p.Fiber (unop U)) :
    (isoClassToPoints Y).app U (Quotient.mk'' x) =
      ULift.up
        (Sets.ofPresheaf.fiberToValue Y.functorOfPoints
          (unop U) x) :=
  sorry

/-- The presheaf map `c` induced by a morphism `π : X ⟶ Y.toGroupoids`, sending a
fiberwise isomorphism class of `X` to the corresponding point of `Y`. -/
noncomputable def isoClassComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids) :
    Functor.fiberIsoClassPresheaf X.p ⟶
      Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  BasedFunctor.fiberIsoClassMap (toBasedFunctor π) ≫
    isoClassToPoints Y

/-- On a represented fiber class, `isoClassComparison π` applies the fiber functor of
`π` and then universe-lifted Grothendieck evaluation. -/
theorem isoClassComparison_app_mk {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids)
    (U : (Over S)ᵒᵖ) (x : X.p.Fiber (unop U)) :
    (isoClassComparison π).app U (Quotient.mk'' x) =
      ULift.up
        (Sets.ofPresheaf.fiberToValue Y.functorOfPoints (unop U)
          ((fiberFunctor π (unop U)).obj x)) :=
  sorry

/-- The sheafified comparison `c^#` obtained by lifting `isoClassComparison π` along
fppf sheafification. -/
noncomputable def isoClassSheafComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids) :
    isoClassSheaf X ⟶ Y.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  (Scheme.fppfTopology.over S).sheafifyLift (isoClassComparison π)
    (functorOfPoints_ulift_isSheaf Y)

/-- The sheafification unit followed by `isoClassSheafComparison π` recovers
`isoClassComparison π`. -/
theorem toSheafify_isoClassSheafComparison {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids) :
    (Scheme.fppfTopology.over S).toSheafify (Functor.fiberIsoClassPresheaf X.p) ≫
        isoClassSheafComparison π =
      isoClassComparison π :=
  sorry

/-- Lemma 101.28.2: let `X` be an algebraic stack. If `X` is a gerbe over an
algebraic space `Y` via `π : X ⟶ Y.toGroupoids`, then the fppf sheafification of
the presheaf `U ↦ Ob(X.p.Fiber U)/≅` is identified with `Y` by an isomorphism of
sheaves, and `X` is a gerbe over that sheafification via `π`. -/
@[stacks 06QD]
theorem isoClassSheafComparison_isIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids)
    [Gerbe π] : IsIso (isoClassSheafComparison π) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
