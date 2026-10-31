/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import ReasLib.Algebra.Homology.ComplexShape
public import ReasLib.Algebra.Homology.Homotopy.Triple
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 01A2

# Functorial cylinders of homological complexes

This file promotes the cylinder construction from a single chain-complex shape to arbitrary
homological complexes.  The action on morphisms is the canonical map between homotopy cofibers
induced by a morphism of their defining arrows.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace HomologicalComplex

variable {ι : Type w} {C : Type u} [Category.{v} C] [Preadditive C]
variable {c : ComplexShape ι} [HasBinaryBiproducts C]

namespace cylinder

/-- The square induced by a morphism of homological complexes commutes with the two defining
arrows of their cylinders. -/
@[stacks 01A2 "cylinder defining-arrow square"]
theorem arrowMap.w {A B : HomologicalComplex C c} (f : A ⟶ B) :
    f ≫ biprod.lift (𝟙 B) (-𝟙 B) =
      biprod.lift (𝟙 A) (-𝟙 A) ≫ biprod.map f f := by
  apply biprod.hom_ext <;> simp [Category.assoc]

/-- A morphism of homological complexes induces a morphism between the arrows whose homotopy
cofibers define their cylinders. -/
@[stacks 01A2 "map of cylinder defining arrows"]
noncomputable def arrowMap {A B : HomologicalComplex C c} (f : A ⟶ B) :
    Arrow.mk (biprod.lift (𝟙 A) (-𝟙 A)) ⟶
      Arrow.mk (biprod.lift (𝟙 B) (-𝟙 B)) where
  left := f
  right := biprod.map f f
  w := arrowMap.w f

/-- The defining-arrow map associated to an identity is the identity square. -/
@[simp, stacks 01A2 "identity cylinder defining-arrow map"]
theorem arrowMap.id (A : HomologicalComplex C c) :
    arrowMap (𝟙 A) = 𝟙 (Arrow.mk (biprod.lift (𝟙 A) (-𝟙 A))) := by
  apply Arrow.hom_ext
  · rfl
  · change biprod.map (𝟙 A) (𝟙 A) = 𝟙 (A ⊞ A)
    apply biprod.hom_ext <;> simp

/-- Defining-arrow maps respect composition. -/
@[stacks 01A2 "composition of cylinder defining-arrow maps"]
theorem arrowMap.comp {A B D : HomologicalComplex C c} (f : A ⟶ B) (g : B ⟶ D) :
    arrowMap (f ≫ g) = arrowMap f ≫ arrowMap g := by
  apply Arrow.hom_ext
  · rfl
  · change biprod.map (f ≫ g) (f ≫ g) = biprod.map f f ≫ biprod.map g g
    apply biprod.hom_ext <;> simp [Category.assoc]

/-- The functor sending a homological complex to the arrow whose homotopy cofiber is its
cylinder. -/
@[stacks 01A2 "cylinder defining-arrow functor"]
noncomputable def arrowFunctor :
    HomologicalComplex C c ⥤ Arrow (HomologicalComplex C c) where
  obj A := Arrow.mk (biprod.lift (𝟙 A) (-𝟙 A))
  map f := arrowMap f
  map_id A := arrowMap.id A
  map_comp f g := arrowMap.comp f g

/-- The object part of the cylinder defining-arrow functor. -/
@[simp, stacks 01A2 "cylinder defining-arrow functor object"]
theorem arrowFunctor_obj (A : HomologicalComplex C c) :
    arrowFunctor.obj A = Arrow.mk (biprod.lift (𝟙 A) (-𝟙 A)) := rfl

/-- The morphism part of the cylinder defining-arrow functor. -/
@[simp, stacks 01A2 "cylinder defining-arrow functor morphism"]
theorem arrowFunctor_map {A B : HomologicalComplex C c} (f : A ⟶ B) :
    arrowFunctor.map f = arrowMap f := rfl

variable [DecidableRel c.Rel] [c.HasIncoming]

/-- The canonical map between cylinders induced by a morphism of homological complexes. -/
@[stacks 01A2 "functorial map between cylinders"]
noncomputable def map {A B : HomologicalComplex C c} (f : A ⟶ B) :
    A.cylinder ⟶ B.cylinder :=
  homotopyCofiber.mapArrowHom
    (biprod.lift (𝟙 A) (-𝟙 A)) (biprod.lift (𝟙 B) (-𝟙 B))
    (ComplexShape.HasIncoming.rightTotal (c := c)) (arrowMap f)

/-- The cylinder map induced by an identity is the identity. -/
@[simp, stacks 01A2 "identity cylinder map"]
theorem map.id (A : HomologicalComplex C c) :
    map (𝟙 A) = 𝟙 A.cylinder := by
  simp only [map, arrowMap.id, homotopyCofiber.mapArrowHom_id]

/-- Cylinder maps respect composition. -/
@[stacks 01A2 "composition of cylinder maps"]
theorem map.comp {A B D : HomologicalComplex C c} (f : A ⟶ B) (g : B ⟶ D) :
    map (f ≫ g) = map f ≫ map g := by
  simp only [map, arrowMap.comp, homotopyCofiber.mapArrowHom_comp]

/-- The cylinder construction as an endofunctor on homological complexes. -/
@[stacks 01A2]
noncomputable def functor : HomologicalComplex C c ⥤ HomologicalComplex C c where
  obj A := A.cylinder
  map f := map f
  map_id A := map.id A
  map_comp f g := map.comp f g

/-- The cylinder functor sends a complex to its canonical cylinder. -/
@[simp, stacks 01A2 "cylinder functor object"]
theorem functor_obj (A : HomologicalComplex C c) :
    functor.obj A = A.cylinder := rfl

/-- The action of the cylinder functor is the map induced between homotopy cofibers. -/
@[simp, stacks 01A2 "cylinder functor morphism"]
theorem functor_map {A B : HomologicalComplex C c} (f : A ⟶ B) :
    functor.map f = map f := rfl

namespace left

set_option backward.isDefEq.respectTransparency false in
/-- The left cylinder inclusion is natural. -/
@[stacks 01A2 "left cylinder inclusion naturality"]
theorem naturality {A B : HomologicalComplex C c} (f : A ⟶ B) :
    (𝟭 (HomologicalComplex C c)).map f ≫ ι₀ B =
      ι₀ A ≫ functor.map f := by
  simp [functor, ι₀, map, homotopyCofiber.mapArrowHom, arrowMap, Arrow.Hom.right,
    Category.assoc]

end left

namespace right

set_option backward.isDefEq.respectTransparency false in
/-- The right cylinder inclusion is natural. -/
@[stacks 01A2 "right cylinder inclusion naturality"]
theorem naturality {A B : HomologicalComplex C c} (f : A ⟶ B) :
    (𝟭 (HomologicalComplex C c)).map f ≫ ι₁ B =
      ι₁ A ≫ functor.map f := by
  simp [functor, ι₁, map, homotopyCofiber.mapArrowHom, arrowMap, Arrow.Hom.right,
    Category.assoc]

end right

namespace projection

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cylinder projection is natural. -/
@[stacks 01A2 "cylinder projection naturality"]
theorem naturality {A B : HomologicalComplex C c} (f : A ⟶ B) :
    functor.map f ≫ π B =
      π A ≫ (𝟭 (HomologicalComplex C c)).map f := by
  have h : biprod.map f f ≫ biprod.desc (𝟙 B) (𝟙 B) =
      biprod.desc (𝟙 A) (𝟙 A) ≫ f := by
    apply biprod.hom_ext' <;> simp
  ext i
  change (map f).f i ≫ (π B).f i = (π A).f i ≫ f.f i
  by_cases hi : c.Rel i (c.next i)
  · apply homotopyCofiber.ext_from_X (biprod.lift (𝟙 A) (-𝟙 A)) _ _ hi
    · simp [map, homotopyCofiber.mapArrowHom, arrowMap, Arrow.Hom.left,
        homotopyCofiber.inrCompHomotopy_hom _ _ _ _ hi, Category.assoc]
    · simpa [map, homotopyCofiber.mapArrowHom, arrowMap, Arrow.Hom.right,
        Category.assoc] using congrArg (fun k => k.f i) h
  · apply homotopyCofiber.ext_from_X' (biprod.lift (𝟙 A) (-𝟙 A)) i hi
    simpa [map, homotopyCofiber.mapArrowHom, arrowMap, Arrow.Hom.right,
      Category.assoc] using congrArg (fun k => k.f i) h

end projection

/-- The left endpoint inclusion as a natural transformation into the cylinder functor. -/
@[stacks 01A2 "left cylinder inclusion natural transformation"]
noncomputable def ι₀.natTrans : 𝟭 (HomologicalComplex C c) ⟶ functor where
  app A := ι₀ A
  naturality := fun {A B} f ↦ left.naturality (C := C) (A := A) (B := B) f

namespace ι₀.natTrans

/-- The component of the left cylinder inclusion is the objectwise left endpoint map. -/
@[simp, stacks 01A2 "left cylinder inclusion natural-transformation component"]
theorem app (A : HomologicalComplex C c) :
    (ι₀.natTrans (C := C)).app A = ι₀ A := rfl

end ι₀.natTrans

/-- The right endpoint inclusion as a natural transformation into the cylinder functor. -/
@[stacks 01A2 "right cylinder inclusion natural transformation"]
noncomputable def ι₁.natTrans : 𝟭 (HomologicalComplex C c) ⟶ functor where
  app A := ι₁ A
  naturality := fun {A B} f ↦ right.naturality (C := C) (A := A) (B := B) f

namespace ι₁.natTrans

/-- The component of the right cylinder inclusion is the objectwise right endpoint map. -/
@[simp, stacks 01A2 "right cylinder inclusion natural-transformation component"]
theorem app (A : HomologicalComplex C c) :
    (ι₁.natTrans (C := C)).app A = ι₁ A := rfl

end ι₁.natTrans

/-- The canonical cylinder projection as a natural transformation. -/
@[stacks 01A2 "cylinder projection natural transformation"]
noncomputable def π.natTrans : functor ⟶ 𝟭 (HomologicalComplex C c) where
  app A := π A
  naturality := fun {A B} f ↦ projection.naturality (C := C) (A := A) (B := B) f

namespace π.natTrans

/-- The component of the cylinder projection is the objectwise canonical projection. -/
@[simp, stacks 01A2 "cylinder projection natural-transformation component"]
theorem app (A : HomologicalComplex C c) :
    (π.natTrans (C := C)).app A = π A := rfl

end π.natTrans

set_option backward.isDefEq.respectTransparency false in
private theorem homotopy₀₁_hom (A : HomologicalComplex C c) (i j : ι)
    (hij : c.Rel j i) :
    (homotopy₀₁ A (ComplexShape.HasIncoming.rightTotal (c := c))).hom i j =
      inlX A i j hij := by
  simp [homotopy₀₁, πCompι₀Homotopy, πCompι₀Homotopy.nullHomotopy,
    Homotopy.equivSubZero, Homotopy.nullHomotopy', Homotopy.nullHomotopy,
    hij, ι₁, Category.assoc]

omit [HasBinaryBiproducts C] [DecidableRel c.Rel] [c.HasIncoming] in
private theorem homotopyTriple_ext {A B : HomologicalComplex C c}
    {x y : HomotopyTriple A B} (hleft : x.left = y.left) (hright : x.right = y.right)
    (hhom : x.homotopy.hom = y.homotopy.hom) : x = y := by
  obtain ⟨a, b, h⟩ := x
  obtain ⟨a', b', h'⟩ := y
  dsimp only at hleft hright hhom
  cases hleft
  cases hright
  have hh : h = h' := by
    ext i j
    exact congrFun (congrFun hhom i) j
  cases hh
  rfl

/-- A map out of a cylinder determines its two endpoint maps and their canonical homotopy. -/
@[stacks 01A2 "endpoint triple of a map out of a cylinder"]
noncomputable def toHomotopyTriple {A B : HomologicalComplex C c}
    (f : A.cylinder ⟶ B) : HomotopyTriple A B where
  left := ι₀ A ≫ f
  right := ι₁ A ≫ f
  homotopy := (homotopy₀₁ A (ComplexShape.HasIncoming.rightTotal (c := c))).compRight f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Descending the endpoint triple associated to a map out of a cylinder recovers that map. -/
@[stacks 01A2 "cylinder descent after endpoint classification"]
theorem desc_toHomotopyTriple {A B : HomologicalComplex C c} (f : A.cylinder ⟶ B) :
    desc (toHomotopyTriple f).left (toHomotopyTriple f).right
      (toHomotopyTriple f).homotopy = f := by
  have h : biprod.desc (ι₀ A ≫ f) (ι₁ A ≫ f) = homotopyCofiber.inr _ ≫ f := by
    apply biprod.hom_ext' <;> simp [ι₀, ι₁, Category.assoc]
  ext i
  by_cases hi : c.Rel i (c.next i)
  · apply homotopyCofiber.ext_from_X (biprod.lift (𝟙 A) (-𝟙 A)) _ _ hi
    · simp [desc, toHomotopyTriple, Homotopy.equivSubZero, homotopy₀₁_hom, hi]
    · simpa only [desc, toHomotopyTriple, homotopyCofiber.inrX_desc_f, comp_f,
        homotopyCofiber.inr_f] using congrArg (fun k => k.f i) h
  · apply homotopyCofiber.ext_from_X' (biprod.lift (𝟙 A) (-𝟙 A)) i hi
    simpa only [desc, toHomotopyTriple, homotopyCofiber.inrX_desc_f, comp_f,
      homotopyCofiber.inr_f] using congrArg (fun k => k.f i) h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking endpoints of the descended map associated to a homotopy triple recovers the triple. -/
@[stacks 01A2 "cylinder endpoint classification after descent"]
theorem toHomotopyTriple_desc {A B : HomologicalComplex C c} (x : HomotopyTriple A B) :
    toHomotopyTriple (desc x.left x.right x.homotopy) = x := by
  apply homotopyTriple_ext
  · exact ι₀_desc _ _ _
  · exact ι₁_desc _ _ _
  · funext i j
    by_cases hij : c.Rel j i
    · simp [toHomotopyTriple, homotopy₀₁_hom, hij, desc, inlX,
        Homotopy.equivSubZero]
    · simp only [Homotopy.zero _ _ _ hij]

/-- Maps out of a cylinder are equivalent to pairs of endpoint maps equipped with a homotopy. -/
@[stacks 01A2 "maps out of a cylinder as homotopy triples"]
noncomputable def homEquiv (A B : HomologicalComplex C c) :
    (A.cylinder ⟶ B) ≃ HomotopyTriple A B where
  toFun := toHomotopyTriple
  invFun x := desc x.left x.right x.homotopy
  left_inv := desc_toHomotopyTriple
  right_inv := toHomotopyTriple_desc

/-- The forward map of the cylinder Hom equivalence is the endpoint-triple construction. -/
@[simp, stacks 01A2 "forward map of the cylinder Hom equivalence"]
theorem homEquiv.apply (A B : HomologicalComplex C c) (f : A.cylinder ⟶ B) :
    homEquiv A B f = toHomotopyTriple f := rfl

/-- The inverse of the cylinder Hom equivalence descends an endpoint triple. -/
@[simp, stacks 01A2 "inverse map of the cylinder Hom equivalence"]
theorem homEquiv.symm_apply (A B : HomologicalComplex C c) (x : HomotopyTriple A B) :
    (homEquiv A B).symm x = desc x.left x.right x.homotopy := rfl

/-- The left endpoint of the cylinder Hom equivalence. -/
@[simp, stacks 01A2 "left endpoint of the cylinder Hom equivalence"]
theorem homEquiv.apply_left (A B : HomologicalComplex C c) (f : A.cylinder ⟶ B) :
    (homEquiv A B f).left = ι₀ A ≫ f := rfl

/-- The right endpoint of the cylinder Hom equivalence. -/
@[simp, stacks 01A2 "right endpoint of the cylinder Hom equivalence"]
theorem homEquiv.apply_right (A B : HomologicalComplex C c) (f : A.cylinder ⟶ B) :
    (homEquiv A B f).right = ι₁ A ≫ f := rfl

/-- The homotopy component of the cylinder Hom equivalence. -/
@[simp, stacks 01A2 "homotopy component of the cylinder Hom equivalence"]
theorem homEquiv.apply_homotopy (A B : HomologicalComplex C c) (f : A.cylinder ⟶ B) :
    (homEquiv A B f).homotopy =
      (homotopy₀₁ A (ComplexShape.HasIncoming.rightTotal (c := c))).compRight f := rfl

/-- The cylinder hom-equivalence sends postcomposition to postcomposition of homotopy
triples. -/
@[stacks 01A2 "postcomposition under the cylinder Hom equivalence"]
theorem homEquiv.comp (A : HomologicalComplex C c) {B D : HomologicalComplex C c}
    (g : B ⟶ D) (f : A.cylinder ⟶ B) :
    homEquiv A D (f ≫ g) =
      (HomotopyTriple.functor A).map g (homEquiv A B f) := by
  apply homotopyTriple_ext
  · change ι₀ A ≫ (f ≫ g) = (ι₀ A ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm
  · change ι₁ A ≫ (f ≫ g) = (ι₁ A ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm
  · funext i j
    change (homotopy₀₁ A (ComplexShape.HasIncoming.rightTotal (c := c))).hom i j ≫
        (f ≫ g).f j =
      ((homotopy₀₁ A (ComplexShape.HasIncoming.rightTotal (c := c))).hom i j ≫ f.f j) ≫ g.f j
    simp only [comp_f, Category.assoc]

/-- The cylinder corepresents the functor of endpoint pairs equipped with a homotopy. -/
@[stacks 01A2]
noncomputable def corepresentableBy (A : HomologicalComplex C c) :
    (HomotopyTriple.functor A).CorepresentableBy A.cylinder where
  homEquiv := fun {B} ↦ homEquiv A B
  homEquiv_comp := homEquiv.comp A

/-- The forward equivalence in cylinder corepresentability is the endpoint-triple map. -/
@[simp, stacks 01A2 "corepresenting cylinder forward map"]
theorem corepresentableBy.homEquiv.apply (A : HomologicalComplex C c)
    {B : HomologicalComplex C c} (f : A.cylinder ⟶ B) :
    (corepresentableBy A).homEquiv f = toHomotopyTriple f := rfl

/-- The inverse equivalence in cylinder corepresentability is homotopy descent. -/
@[simp, stacks 01A2 "corepresenting cylinder inverse map"]
theorem corepresentableBy.homEquiv.symm_apply (A : HomologicalComplex C c)
    {B : HomologicalComplex C c} (x : HomotopyTriple A B) :
    ((corepresentableBy A).homEquiv).symm x =
      desc x.left x.right x.homotopy := rfl

end cylinder

end HomologicalComplex
