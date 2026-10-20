module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (zbar : GeometricPoint Z)

/-- Same-field geometric points of `X` over `zbar` via `f ≫ g` correspond to a
point of `Y` over `zbar` together with a point of `X` over that point. -/
def Fiber.compEquiv :
    Fiber (f ≫ g) zbar ≃ (y : Fiber g zbar) × Fiber f y.point where
  toFun x :=
    let y := Fiber.of (j := g) (xbar := zbar) (x.lift ≫ f)
      (Eq.trans (Category.assoc x.lift f g) x.fac)
    ⟨y, Fiber.of (j := f) (xbar := y.point) x.lift rfl⟩
  invFun p :=
    Fiber.of (j := f ≫ g) (xbar := zbar) p.2.lift
      (Eq.trans (Eq.trans (Eq.symm (Category.assoc p.2.lift f g))
            (congrArg (fun t ↦ t ≫ g) p.2.fac))
        (Eq.trans (congrArg (fun t ↦ t ≫ g) p.1.point_hom) p.1.fac))
  left_inv := sorry
  right_inv := sorry

/-- The first factor of `Fiber.compEquiv` is composition with `f`. -/
theorem Fiber.compEquiv_fst (x : Fiber (f ≫ g) zbar) :
    (Fiber.compEquiv f g zbar x).1.lift = x.lift ≫ f :=
  rfl

/-- The second factor of `Fiber.compEquiv` recovers the morphism to `X`. -/
theorem Fiber.compEquiv_snd (x : Fiber (f ≫ g) zbar) :
    (Fiber.compEquiv f g zbar x).2.lift = x.lift :=
  rfl

/-- The geometric point of `X` is unchanged by `Fiber.compEquiv`. -/
theorem Fiber.compEquiv_point (x : Fiber (f ≫ g) zbar) :
    (Fiber.compEquiv f g zbar x).2.point = x.point :=
  rfl

end AlgebraicGeometry.Scheme.GeometricPoint


end
