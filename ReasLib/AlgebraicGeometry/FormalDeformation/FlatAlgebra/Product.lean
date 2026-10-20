module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic

/-!
# Equibased products of algebra deformation categories

Families of deformations with a common Artinian local base have factor
projections, pairing, and factorwise transport by based functors.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {ι : Type u}

/-- The product of ring deformation categories over `ArtinianLocalAlgCat`,
with objects `(A, x i)` where each `x i` is a deformation of `R i` over the same
base `A`. -/
def deformationPi (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    Type (u + 1) :=
  (A : ArtinianLocalAlgCat Λ k) × ∀ i, (deformationForget Λ k (R i)).Fiber A

/-- Package an equibased family of ring deformations as an object of `deformationPi`. -/
def deformationPi.mk (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (A : ArtinianLocalAlgCat Λ k) (x : ∀ i, deformationCategory Λ k (R i))
    (hx : ∀ i, (deformationForget Λ k (R i)).obj (x i) = A) :
    deformationPi Λ k R :=
  ⟨A, fun i ↦ Fiber.mk (hx i)⟩

/-- The stored Artinian local base of a packaged equibased family. -/
theorem deformationPi.mk_base (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (A : ArtinianLocalAlgCat Λ k) (x : ∀ i, deformationCategory Λ k (R i))
    (hx : ∀ i, (deformationForget Λ k (R i)).obj (x i) = A) :
    (deformationPi.mk Λ k R A x hx).1 = A :=
  rfl

/-- The stored deformation of `R i` in a packaged equibased family. -/
theorem deformationPi.mk_fiber (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (A : ArtinianLocalAlgCat Λ k) (x : ∀ i, deformationCategory Λ k (R i))
    (hx : ∀ i, (deformationForget Λ k (R i)).obj (x i) = A) (i : ι) :
    Fiber.fiberInclusion.obj ((deformationPi.mk Λ k R A x hx).2 i) = x i :=
  rfl

variable {R : ι → Type u} [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]

/-- Morphisms in `deformationPi` are a base map together with a family of
deformation morphisms. -/
def deformationPiHom (X Y : deformationPi Λ k R) : Type u :=
  (f : X.1 ⟶ Y.1) ×
    ∀ i, { φ : Fiber.fiberInclusion.obj (X.2 i) ⟶ Fiber.fiberInclusion.obj (Y.2 i) //
      (deformationForget Λ k (R i)).map φ =
        eqToHom (X.2 i).property ≫ f ≫ eqToHom (Y.2 i).property.symm }

/-- The identity morphism of an equibased family of deformations. -/
def deformationPiHom.id (X : deformationPi Λ k R) : deformationPiHom Λ k X X :=
  ⟨𝟙 X.1, fun i ↦ ⟨𝟙 (Fiber.fiberInclusion.obj (X.2 i)), sorry⟩⟩

/-- Composition of morphisms of equibased families of deformations. -/
def deformationPiHom.comp {X Y Z : deformationPi Λ k R} (f : deformationPiHom Λ k X Y)
    (g : deformationPiHom Λ k Y Z) : deformationPiHom Λ k X Z :=
  ⟨f.1 ≫ g.1, fun i ↦ ⟨(f.2 i).1 ≫ (g.2 i).1, sorry⟩⟩

/-- Identity is a left identity for morphisms of equibased deformation families. -/
theorem deformationPiHom.id_comp {X Y : deformationPi Λ k R}
    (f : deformationPiHom Λ k X Y) :
    deformationPiHom.comp Λ k (deformationPiHom.id Λ k X) f = f := sorry

/-- Identity is a right identity for morphisms of equibased deformation families. -/
theorem deformationPiHom.comp_id {X Y : deformationPi Λ k R}
    (f : deformationPiHom Λ k X Y) :
    deformationPiHom.comp Λ k f (deformationPiHom.id Λ k Y) = f := sorry

/-- Composition of equibased deformation morphisms is associative. -/
theorem deformationPiHom.assoc {W X Y Z : deformationPi Λ k R}
    (f : deformationPiHom Λ k W X) (g : deformationPiHom Λ k X Y)
    (h : deformationPiHom Λ k Y Z) :
    deformationPiHom.comp Λ k (deformationPiHom.comp Λ k f g) h =
      deformationPiHom.comp Λ k f (deformationPiHom.comp Λ k g h) := sorry

/-- The category of equibased families of ring deformations. -/
instance deformationPiCategory : Category.{u} (deformationPi Λ k R) where
  Hom := deformationPiHom Λ k
  id := deformationPiHom.id Λ k
  comp f g := deformationPiHom.comp Λ k f g
  id_comp := deformationPiHom.id_comp Λ k
  comp_id := deformationPiHom.comp_id Λ k
  assoc := deformationPiHom.assoc Λ k

variable (R) in
/-- The projection `∏_{C_Λ} Def_{R i} ⥤ C_Λ` sending `(A, x i)` to `A`. -/
def deformationPiForget : deformationPi Λ k R ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.1
  map f := f.1
  map_id := sorry
  map_comp := sorry

/-- `deformationPiForget` evaluates to the stored Artinian local base. -/
theorem deformationPiForget_obj (X : deformationPi Λ k R) :
    (deformationPiForget Λ k R).obj X = X.1 :=
  rfl

variable (R) in
/-- The slice projection of `deformationPi` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationPiForget_op :
    IsFibered.InGroupoids (deformationPiForget Λ k R).op :=
  sorry

variable (R) in
/-- The based functor projecting `∏_{C_Λ} Def_{R i}` onto the factor `Def_{R i}`. -/
def evalBasedFunctor (i : ι) :
    BasedCategory.ofFunctor (deformationPiForget Λ k R) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (R i)) where
  toFunctor :=
    { obj X := Fiber.fiberInclusion.obj (X.2 i)
      map f := (f.2 i).1
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- The underlying functor of `evalBasedFunctor` evaluates the `i`-th stored deformation. -/
theorem evalBasedFunctor_toFunctor (i : ι) (X : deformationPi Λ k R) :
    (evalBasedFunctor Λ k R i).toFunctor.obj X = Fiber.fiberInclusion.obj (X.2 i) :=
  rfl

variable (R) in
/-- Pair a family of based functors into `Def_{R i}` over a common projection `p`
into a single based functor landing in `deformationPi`. -/
def pairing {F : Type (u + 1)} [Category.{u} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (φ : ∀ i, BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (deformationForget Λ k (R i))) :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (deformationPiForget Λ k R) where
  toFunctor :=
    { obj x := ⟨p.obj x, fun i ↦ ⟨(φ i).obj x, (φ i).w_obj x⟩⟩
      map f := ⟨p.map f, fun i ↦ ⟨(φ i).map f, sorry⟩⟩
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- The underlying functor of `pairing` retains the common base object of `p`. -/
theorem pairing_toFunctor {F : Type (u + 1)} [Category.{u} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (φ : ∀ i, BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (deformationForget Λ k (R i)))
    (x : F) :
    ((pairing Λ k R p φ).toFunctor.obj x).1 = p.obj x :=
  rfl

/-- The assembled pairing lies over the original projection `p`. -/
theorem pairing_w {F : Type (u + 1)} [Category.{u} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (φ : ∀ i, BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (deformationForget Λ k (R i))) :
    (pairing Λ k R p φ).toFunctor ⋙ deformationPiForget Λ k R = p :=
  (pairing Λ k R p φ).w

variable (R) in
/-- Apply a family of based functors `Def_{R i} ⥤ᵇ Def_{S i}` factorwise to
`deformationPi`. -/
def deformationPiMap (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)]
    (φ : ∀ i, BasedCategory.ofFunctor (deformationForget Λ k (R i)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (S i))) :
    BasedCategory.ofFunctor (deformationPiForget Λ k R) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k S) where
  toFunctor :=
    { obj X := ⟨X.1, fun i ↦ ⟨(φ i).obj (Fiber.fiberInclusion.obj (X.2 i)),
        ((φ i).w_obj (Fiber.fiberInclusion.obj (X.2 i))).trans (X.2 i).property⟩⟩
      map f := ⟨f.1, fun i ↦ ⟨(φ i).map (f.2 i).1, sorry⟩⟩
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- Factorwise maps of deformation products retain the common Artinian base. -/
theorem deformationPiMap_obj_base (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)]
    (φ : ∀ i, BasedCategory.ofFunctor (deformationForget Λ k (R i)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (S i)))
    (X : deformationPi Λ k R) :
    ((deformationPiMap Λ k R S φ).toFunctor.obj X).1 = X.1 :=
  rfl

end FlatAlgebraCat

end
