/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Types
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Topology.Sheaves.PUnit

/-!
# The canonical point of the jointly-surjective site on types

The canonical point is deliberately modeled with the strict identity fiber.
This avoids replacing downstream definitional equalities by merely natural
isomorphisms to the generic local-site point.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor

universe w

namespace CategoryTheory.GrothendieckTopology.Point

namespace TypesPoint

/-- The strict identity fiber functor of the canonical point of the site of types. -/
abbrev fiber : Type w ⥤ Type w := 𝟭 _

/-- The category of elements of the identity fiber is cofiltered. -/
theorem isCofiltered : IsCofiltered fiber.Elements := sorry

/-- The category of elements of the identity fiber is initially small. -/
theorem initiallySmall : InitiallySmall.{w} fiber.Elements := sorry

/-- Covering sieves for the jointly-surjective topology act jointly surjectively on the identity
fiber. -/
theorem jointlySurjective
    {X : Type w} (R : Sieve X) (hR : R ∈ typesGrothendieckTopology X)
    (x : fiber.obj X) :
    ∃ (Y : Type w) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x := sorry

end TypesPoint

/-- The canonical point of the jointly-surjective Grothendieck topology on `Type`.

Its fiber is the strict identity functor `TypesPoint.fiber`; keeping this bundled owner opaque
preserves Mathlib's canonical element-category colimit instance. -/
noncomputable def typesPoint : Point.{w} typesGrothendieckTopology.{w} where
  fiber := TypesPoint.fiber
  isCofiltered := TypesPoint.isCofiltered
  initiallySmall := TypesPoint.initiallySmall
  jointly_surjective := TypesPoint.jointlySurjective

namespace TypesPoint

/-- The distinguished element of the strict type-point fiber over `PUnit`. -/
noncomputable abbrev baseObj : typesPoint.{w}.fiber.Elements :=
  typesPoint.{w}.fiber.elementsMk PUnit.{w + 1} PUnit.unit

/-- The canonical map from `PUnit` satisfies the element-category compatibility condition. -/
theorem baseTo_condition (Y : typesPoint.{w}.fiber.Elements) :
    fiber.map (↾fun _ ↦ Y.2) PUnit.unit = Y.2 := sorry

/-- The canonical arrow from the distinguished `PUnit` element to an arbitrary fiber element. -/
noncomputable def baseTo (Y : typesPoint.{w}.fiber.Elements) : baseObj.{w} ⟶ Y :=
  ⟨↾fun _ ↦ Y.2, baseTo_condition.{w} Y⟩

/-- Every arrow from the distinguished `PUnit` element is the canonical one. -/
theorem baseTo_unique (Y : typesPoint.{w}.fiber.Elements) (f : baseObj.{w} ⟶ Y) :
    f = baseTo.{w} Y := sorry

/-- Maps from the distinguished `PUnit` element are uniquely determined. -/
noncomputable instance uniqueBaseHom (Y : typesPoint.{w}.fiber.Elements) :
    Unique (baseObj.{w} ⟶ Y) where
  default := baseTo.{w} Y
  uniq := baseTo_unique.{w} Y

/-- The distinguished `PUnit` element is initial in the category of elements of the strict
type-point fiber. -/
noncomputable def baseInitial : IsInitial baseObj.{w} :=
  IsInitial.ofUnique _

/-- The opposite of the distinguished `PUnit` element is terminal in the opposite element
category. -/
noncomputable abbrev baseTerminalObj : typesPoint.{w}.fiber.Elementsᵒᵖ :=
  op baseObj.{w}

/-- The terminality witness for the opposite distinguished element. -/
noncomputable def baseTerminal : IsTerminal baseTerminalObj.{w} :=
  terminalOpOfInitial baseInitial.{w}

/-- The element-category diagram whose colimit computes the presheaf fiber of the strict type
point. -/
noncomputable abbrev presheafFiberDiagram (P : Type wᵒᵖ ⥤ Type w) :
    typesPoint.{w}.fiber.Elementsᵒᵖ ⥤ Type w :=
  (CategoryOfElements.π typesPoint.{w}.fiber).op ⋙ P

/-- The presheaf fiber of the strict type point is evaluation at `PUnit`, objectwise. -/
noncomputable def presheafFiberObjIso (P : Type wᵒᵖ ⥤ Type w) :
    typesPoint.{w}.presheafFiber.obj P ≅ P.obj (op PUnit.{w + 1}) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal baseTerminal.{w} (presheafFiberDiagram.{w} P))

/-- The objectwise evaluation comparison is natural in the presheaf. -/
theorem presheafFiberObjIso_naturality
    {P Q : Type wᵒᵖ ⥤ Type w} (f : P ⟶ Q) :
    typesPoint.{w}.presheafFiber.map f ≫ (presheafFiberObjIso.{w} Q).hom =
      (presheafFiberObjIso.{w} P).hom ≫
        ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit.{w + 1})).map f := sorry

/-- The presheaf fiber of the strict type point is evaluation at `PUnit`. -/
noncomputable def presheafFiberIso :
    typesPoint.{w}.presheafFiber ≅
      (evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit.{w + 1}) :=
  NatIso.ofComponents (fun P ↦ presheafFiberObjIso.{w} P)
    (fun f ↦ presheafFiberObjIso_naturality.{w} f)

/-- The sheaf fiber of the strict type point is the inverse of the canonical equivalence with
`Type`. -/
@[stacks 04EL "(1)"]
noncomputable def sheafFiberIso :
    typesPoint.{w}.sheafFiber ≅ typeEquiv.{w}.inverse :=
  Functor.isoWhiskerLeft (sheafToPresheaf typesGrothendieckTopology (Type w))
    presheafFiberIso.{w}

/-- The skyscraper sheaf functor of the strict type point is the canonical equivalence from
`Type` to sheaves on the jointly-surjective site. -/
noncomputable def skyscraperSheafFunctorIso :
    typeEquiv.{w}.functor ≅ typesPoint.{w}.skyscraperSheafFunctor :=
  (conjugateIsoEquiv typeEquiv.{w}.symm.toAdjunction typesPoint.{w}.skyscraperSheafAdjunction)
    sheafFiberIso.{w}

end TypesPoint

end CategoryTheory.GrothendieckTopology.Point
