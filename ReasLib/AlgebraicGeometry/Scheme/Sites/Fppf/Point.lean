module

public import ReasLib.RingTheory.Fppf.Local
public import ReasLib.CategoryTheory.Sites.Point.Initial
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.FppfPoint

/-- The affine object associated to a ring map. -/
noncomputable def specObj {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (Scheme.Spec.obj (op (CommRingCat.of A))).AffineOver :=
  Scheme.AffineOver.mk (Scheme.Spec.obj (op (CommRingCat.of B))) inferInstance
    (Spec.map (CommRingCat.ofHom f))

/-- The underlying affine scheme of the object associated to a ring map. -/
theorem specObj_obj {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (Scheme.AffineOver.toScheme (Scheme.Spec.obj (op (CommRingCat.of A)))).obj (specObj f) =
      Scheme.Spec.obj (op (CommRingCat.of B)) := sorry

/-- The structure morphism of the affine object associated to a ring map. -/
theorem specObj_hom {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (Scheme.AffineOver.obj (specObj f)).hom = Spec.map (CommRingCat.ofHom f) := sorry

/-- The represented fiber functor associated to a ring map. -/
abbrev fiber {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (Scheme.Spec.obj (op (CommRingCat.of A))).AffineOver ⥤ Type (u + 1) :=
  shrinkYoneda.{u + 1}.flip.obj (op (specObj f))

/-- Cover lifting for the represented fiber is equivalent to fppf-locality. -/
theorem coversLift_iff {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    GrothendieckTopology.Point.Fiber.coversLift
        (Scheme.bigAffineFppfTopology (Scheme.Spec.obj (op (CommRingCat.of A)))) (fiber f) ↔
      IsFppfLocalRing B := sorry

/-- The represented point associated to an fppf-local algebra. -/
noncomputable def of {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hB : IsFppfLocalRing B) :
    GrothendieckTopology.Point.{u + 1}
      (Scheme.bigAffineFppfTopology (Scheme.Spec.obj (op (CommRingCat.of A)))) where
  fiber := fiber f
  isCofiltered := (GrothendieckTopology.pointBot.{u + 1} (specObj f)).isCofiltered
  initiallySmall := (GrothendieckTopology.pointBot.{u + 1} (specObj f)).initiallySmall
  jointly_surjective := (coversLift_iff f).2 hB

/-- The fiber of the represented point is the displayed represented functor. -/
@[simp]
theorem of_fiber {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hB : IsFppfLocalRing B) : (of f hB).fiber = fiber f := sorry

/-- A limiting neighborhood with point `c.pt` is initial in the fiber category. -/
noncomputable def initialOfLimitCone {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {p : GrothendieckTopology.Point.{u + 1}
      (Scheme.bigAffineFppfTopology (Scheme.Spec.obj (op (CommRingCat.of A))))}
    {c : Cone (CategoryOfElements.π p.fiber)} (hpt : c.pt = specObj f)
    (hc : IsLimit c) (x : p.fiber.obj c.pt)
    (hx : ∀ U : p.fiber.Elements,
      p.fiber.map (c.π.app U) x = U.2) :
    IsInitial (p.fiber.elementsMk c.pt x) :=
  CategoryTheory.GrothendieckTopology.Point.initialOfLimitCone p hc x hx

/-- Evaluation at an initial neighborhood computes the sheaf fiber of an affine fppf point. -/
noncomputable def sheafFiberIsoOfInitial {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B)
    {p : GrothendieckTopology.Point.{u + 1}
      (Scheme.bigAffineFppfTopology (Scheme.Spec.obj (op (CommRingCat.of A))))}
    {c : Cone (CategoryOfElements.π p.fiber)} (hpt : c.pt = specObj f)
    {x : p.fiber.obj c.pt} (h : IsInitial (p.fiber.elementsMk c.pt x)) :
    p.sheafFiber (A := Type (u + 1)) ≅
      sheafToPresheaf (Scheme.bigAffineFppfTopology
        (Scheme.Spec.obj (op (CommRingCat.of A)))) (Type (u + 1)) ⋙
        (CategoryTheory.evaluation
          ((Scheme.Spec.obj (op (CommRingCat.of A))).AffineOver)ᵒᵖ
          (Type (u + 1))).obj (op c.pt) :=
  CategoryTheory.GrothendieckTopology.Point.sheafFiberIsoOfInitial p h

/-- The represented point has the expected presheaf-fiber evaluation isomorphism. -/
noncomputable def presheafFiberIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hB : IsFppfLocalRing B) :
    (of f hB).presheafFiber (A := Type (u + 1)) ≅
      (CategoryTheory.evaluation
        ((Scheme.Spec.obj (op (CommRingCat.of A))).AffineOver)ᵒᵖ
        (Type (u + 1))).obj (op (specObj f)) :=
  CategoryTheory.GrothendieckTopology.Point.presheafFiberIsoOfInitial
    (of f hB)
    (Functor.Elements.isInitialElementsMkShrinkYonedaObjObjEquivId.{u + 1} (specObj f))

/-- The represented point has the expected sheaf-fiber evaluation isomorphism. -/
noncomputable def sheafFiberIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hB : IsFppfLocalRing B) :
    (of f hB).sheafFiber (A := Type (u + 1)) ≅
      sheafToPresheaf (Scheme.bigAffineFppfTopology
        (Scheme.Spec.obj (op (CommRingCat.of A))))
          (Type (u + 1)) ⋙
        (CategoryTheory.evaluation
          ((Scheme.Spec.obj (op (CommRingCat.of A))).AffineOver)ᵒᵖ
          (Type (u + 1))).obj (op (specObj f)) :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf (Scheme.bigAffineFppfTopology
      (Scheme.Spec.obj (op (CommRingCat.of A)))) (Type (u + 1)))
      (presheafFiberIso f hB)

/-- A represented affine fppf point exists exactly when the target ring is local and every
faithfully flat, finitely presented extension of it admits a retraction. -/
theorem exists_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (∃ p : GrothendieckTopology.Point.{u + 1}
        (Scheme.bigAffineFppfTopology
          (Scheme.Spec.obj (op (CommRingCat.of A)))),
      p.fiber = fiber f) ↔
      IsLocalRing B ∧
        (∀ (B' : Type u) [CommRing B'] (g : B →+* B'),
          g.FaithfullyFlat → g.FinitePresentation →
            ∃ r : B' →+* B, r.comp g = RingHom.id B) := sorry

end AlgebraicGeometry.Scheme.FppfPoint

end
