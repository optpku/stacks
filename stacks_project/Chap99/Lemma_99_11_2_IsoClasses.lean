/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap99.Lemma_99_10_1_Picard
public import stacks_project.Chap99.Situation_99_11_1_Functor

/-!
# Fibrewise isomorphism classes of the Picard stack over `(Sch/B)`

The projection `Picard.Obj f ⥤ SchemesOver B` displays the Picard stack on
schemes over `B`. Its fibrewise isomorphism-class presheaf compares canonically
with `T ↦ Pic(X_T)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.CohStack (SchemesOver fiber)
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The projection `(T, g, L) ↦ T` from the Picard category of `f` to schemes
over `B`. -/
def toSchemesOver (f : X ⟶ B) : Obj f ⥤ SchemesOver B where
  obj x := x.σ
  map α := α.base
  map_id := sorry
  map_comp := sorry

/-- The object part of `toSchemesOver` is the test scheme of a Picard object. -/
theorem toSchemesOver_obj (f : X ⟶ B) (x : Obj f) :
    (toSchemesOver f).obj x = x.σ := sorry

/-- The morphism part of `toSchemesOver` is the underlying map of schemes over
`B`. -/
theorem toSchemesOver_map {f : X ⟶ B} {x y : Obj f} (α : x ⟶ y) :
    (toSchemesOver f).map α = α.base := sorry

/-- Forgetting the structure map of a scheme over `B` recovers the Picard
projection to `Over S`. -/
theorem toSchemesOver_comp_proj (f : X ⟶ B) :
    toSchemesOver f ⋙ CostructuredArrow.proj (ofOverFunctor S) B = p f := sorry

/-- The Picard projection to schemes over `B` is fibered in groupoids. -/
instance toSchemesOver_isFiberedInGroupoids (f : X ⟶ B) :
    Functor.IsFibered.InGroupoids (toSchemesOver f) := sorry

/-- The invertible module on `X_T` obtained by transporting the line of a fibre
object along the equality of test schemes. -/
def fiberLine {f : X ⟶ B} {σ : SchemesOver B} (x : (toSchemesOver f).Fiber σ) :
    (fiber f σ).Modules :=
  (Modules.pullback (eqToHom (congrArg (fiber f) x.property.symm))).obj x.val.line

/-- Transport of a fibre object's line along the equality of bases preserves
tensor-invertibility. -/
instance fiberLine_isInvertible {f : X ⟶ B} {σ : SchemesOver B}
    (x : (toSchemesOver f).Fiber σ) : isInvertibleObject (fiberLine x) := sorry

/-- Isomorphic objects in a Picard fibre determine the same Picard class. -/
theorem fiberLine_picardClass_iso {f : X ⟶ B} {σ : SchemesOver B}
    {x y : (toSchemesOver f).Fiber σ} (h : Nonempty (x ≅ y)) :
    Modules.picardClass (fiberLine x) = Modules.picardClass (fiberLine y) := sorry

/-- The Picard class of a fibre object, after transporting its line to `X_T`. -/
def fiberObjPicardClass {f : X ⟶ B} {σ : SchemesOver B}
    (x : (toSchemesOver f).Fiber σ) : (fiber f σ).PicardGroup :=
  Modules.picardClass (fiberLine x)

/-- The Picard class of a fibre object is the class of its transported line. -/
theorem fiberObjPicardClass_eq {f : X ⟶ B} {σ : SchemesOver B}
    (x : (toSchemesOver f).Fiber σ) :
    fiberObjPicardClass x = Modules.picardClass (fiberLine x) := sorry

/-- The canonical map sending a fibrewise isomorphism class of invertible sheaves
on `X_T` to the corresponding class in `Pic(X_T)`. -/
def fiberIsoClassToPresheaf (f : X ⟶ B) :
    Functor.fiberIsoClassPresheaf (toSchemesOver f) ⟶ RelativePicard.presheaf f where
  app σ :=
    TypeCat.ofHom <|
      Quotient.lift (fun x ↦ fiberObjPicardClass x)
        (fun x y h ↦ fiberLine_picardClass_iso h)
  naturality := sorry

/-- The inverse comparison sending a Picard class on `X_T` to the isomorphism
class of a chosen invertible representative, viewed in the fibre over `T`. -/
def presheafToFiberIsoClass (f : X ⟶ B) :
    RelativePicard.presheaf f ⟶ Functor.fiberIsoClassPresheaf (toSchemesOver f) where
  app σ :=
    TypeCat.ofHom fun x ↦
      Quotient.mk''
        (⟨ofLine σ.unop (PicardGroup.repr x), rfl⟩ : (toSchemesOver f).Fiber σ.unop)
  naturality := sorry

/-- On a represented fibre object, `fiberIsoClassToPresheaf` evaluates to the
Picard class of the transported line. -/
theorem fiberIsoClassToPresheaf_app_mk (f : X ⟶ B) {σ : SchemesOver B}
    (x : (toSchemesOver f).Fiber σ) :
    (fiberIsoClassToPresheaf f).app (op σ) (Quotient.mk'' x) =
      fiberObjPicardClass x := sorry

/-- `presheafToFiberIsoClass` sends a Picard class to the fibrewise isomorphism
class of `ofLine` of its chosen representative. -/
theorem presheafToFiberIsoClass_app (f : X ⟶ B) (σ : SchemesOver B)
    (x : (fiber f σ).PicardGroup) :
    (presheafToFiberIsoClass f).app (op σ) x =
      Quotient.mk'' ⟨ofLine σ (PicardGroup.repr x), rfl⟩ := sorry

/-- The comparison `Ob(fibre)/≅ → Pic(X_T)` is inverse to the representative
class map. -/
theorem fiberIsoClassToPresheaf_comp_inv (f : X ⟶ B) :
    fiberIsoClassToPresheaf f ≫ presheafToFiberIsoClass f = 𝟙 _ := sorry

/-- The representative class map is inverse to `Ob(fibre)/≅ → Pic(X_T)`. -/
theorem fiberIsoClassInv_comp_toPresheaf (f : X ⟶ B) :
    presheafToFiberIsoClass f ≫ fiberIsoClassToPresheaf f = 𝟙 _ := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
