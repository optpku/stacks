module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Point
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

/- Remark 59.30.2 (1): a compatible limiting neighborhood is initial. -/
@[stacks 06VY] #check
  (AlgebraicGeometry.Scheme.FppfPoint.initialOfLimitCone :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      {p : GrothendieckTopology.Point.{u + 1}
        (Scheme.bigAffineFppfTopology (Scheme.Spec.obj (op (CommRingCat.of A))))}
      {c : Cone (CategoryOfElements.π p.fiber)}, c.pt =
        AlgebraicGeometry.Scheme.FppfPoint.specObj f → IsLimit c →
      (x : p.fiber.obj c.pt) →
      (∀ U : p.fiber.Elements, p.fiber.map (c.π.app U) x = U.2) →
      IsInitial (p.fiber.elementsMk c.pt x))

/- In the affine specialization, the limiting cone records the stalk presentation
`B = colim C` together with the compatible neighborhood elements `x_C`. -/

/- Remark 59.30.2 (2): an initial neighborhood computes sheaf evaluation. -/
@[stacks 06VY] #check
  (AlgebraicGeometry.Scheme.FppfPoint.sheafFiberIsoOfInitial :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      {p : GrothendieckTopology.Point.{u + 1}
        (Scheme.bigAffineFppfTopology (Scheme.Spec.obj (op (CommRingCat.of A))))}
      {c : Cone (CategoryOfElements.π p.fiber)}, c.pt =
        AlgebraicGeometry.Scheme.FppfPoint.specObj f →
      {x : p.fiber.obj c.pt} → IsInitial (p.fiber.elementsMk c.pt x) →
      CategoryTheory.Iso
        (CategoryTheory.GrothendieckTopology.Point.sheafFiber
          (A := Type (u + 1)) p)
        (sheafToPresheaf (Scheme.bigAffineFppfTopology
          (Scheme.Spec.obj (op (CommRingCat.of A)))) (Type (u + 1)) ⋙
          (CategoryTheory.evaluation
            ((Scheme.Spec.obj (op (CommRingCat.of A))).AffineOver)ᵒᵖ
            (Type (u + 1))).obj (op c.pt)))

/- Remark 59.30.2 (3): the represented affine fppf point is characterized by locality and
splitting of faithfully flat finitely presented ring maps. -/
@[stacks 06VY] #check
  (AlgebraicGeometry.Scheme.FppfPoint.exists_iff :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B),
      (∃ p : GrothendieckTopology.Point.{u + 1}
          (Scheme.bigAffineFppfTopology
            (Scheme.Spec.obj (op (CommRingCat.of A)))),
        p.fiber = AlgebraicGeometry.Scheme.FppfPoint.fiber f) ↔
      IsLocalRing B ∧
        (∀ (B' : Type u) [CommRing B'] (g : B →+* B'),
          g.FaithfullyFlat → g.FinitePresentation →
            ∃ r : B' →+* B, r.comp g = RingHom.id B))
