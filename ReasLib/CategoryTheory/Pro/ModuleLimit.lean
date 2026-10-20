module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import ReasLib.CategoryTheory.Pro.HomColimit
public import ReasLib.CategoryTheory.InverseSystem.Positive.ModuleCat.Limits

/-!
# Module-valued realization of presented pro-morphisms

A compatible family in the source limit evaluates every Hom-colimit class.
Precomposition by the actual pro-morphism and evaluation on target identity
classes then gives the target family. No representative of a pro-morphism is
chosen, and no realization functor is supplied as an input.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
universe u w

namespace CategoryTheory.Pro.ModuleLimit

variable {k : Type u} [Field k] {C : Type w} [Category.{u + 1} C]
variable (H : C ⥤ ModuleCat.{u} k)

/-- The module functor with its underlying carrier lifted to the Hom universe
of C, so it can be evaluated on Hom-colimit classes without a smallness cast. -/
def carrierFunctor : C ⥤ Type (u + 1) :=
  H ⋙ forget (ModuleCat.{u} k) ⋙ uliftFunctor.{u + 1, u}

/-- A source limit element evaluates a stage morphism by applying H and the
corresponding limit projection. Coyoneda supplies target naturality. -/
def evaluationCocone (A : PNatInverseSystem C)
    (x : (limit (A ⋙ H) : ModuleCat.{u} k)) : Cocone (A.op ⋙ coyoneda) where
  pt := carrierFunctor H
  ι :=
    { app := fun n ↦ coyonedaEquiv.symm
        (ULift.up ((limit.π (A ⋙ H) n.unop).hom x))
      naturality := sorry }

/-- Evaluation of Hom-colimit classes is the descent of the actual stage
evaluation cocone. -/
def evaluation (A : PNatInverseSystem C)
    (x : (limit (A ⋙ H) : ModuleCat.{u} k)) :
    Pro.homColimit A ⟶ carrierFunctor H :=
  colimit.desc (A.op ⋙ coyoneda) (evaluationCocone H A x)

/-- At each target stage, evaluate the pro-morphism on its identity class,
then evaluate the resulting source Hom-colimit class on x. -/
def componentFun {A B : PNatInverseSystem C}
    (f : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B)
    (n : OrderDual ℕ+) (x : (limit (A ⋙ H) : ModuleCat.{u} k)) : H.obj (B.obj n) :=
  ((evaluation H A x).app (B.obj n)
    ((Pro.homColimit.map f).app (B.obj n)
      ((colimit.ι (B.op ⋙ coyoneda) (op n)).app (B.obj n) (𝟙 (B.obj n))))).down

/-- Evaluation on a fixed pro-morphism class is additive in the source family. -/
theorem componentFun_add {A B : PNatInverseSystem C}
    (f : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B)
    (n : OrderDual ℕ+) (x y : (limit (A ⋙ H) : ModuleCat.{u} k)) :
    componentFun H f n (x + y) = componentFun H f n x + componentFun H f n y := sorry

/-- Evaluation on a fixed pro-morphism class preserves the ground-field action. -/
theorem componentFun_smul {A B : PNatInverseSystem C}
    (f : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B)
    (n : OrderDual ℕ+) (a : k) (x : (limit (A ⋙ H) : ModuleCat.{u} k)) :
    componentFun H f n (a • x) = a • componentFun H f n x := sorry

/-- The specified target component of the realized morphism is linear. -/
def component {A B : PNatInverseSystem C}
    (f : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B)
    (n : OrderDual ℕ+) : limit (A ⋙ H) ⟶ H.obj (B.obj n) :=
  ModuleCat.ofHom
    { toFun := componentFun H f n
      map_add' := componentFun_add H f n
      map_smul' := componentFun_smul H f n }

/-- The actual target components form a cone; compatibility is a law of the
represented-Hom action, not a premise imposed on the pro-morphism. -/
def targetCone {A B : PNatInverseSystem C}
    (f : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B) :
    Cone (B ⋙ H) where
  pt := limit (A ⋙ H)
  π := { app := component H f, naturality := sorry }

/-- The module-limit map of an actual presented pro-morphism. -/
def map {A B : PNatInverseSystem C}
    (f : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B) :
    limit (A ⋙ H) ⟶ limit (B ⋙ H) :=
  limit.lift (B ⋙ H) (targetCone H f)

/-- Realization on a pro-morphism represented by a natural transformation is
the ordinary limit map of its postcomposition with H. -/
theorem map_of_natTrans {A B : PNatInverseSystem C} (a : A ⟶ B) :
    map H ((@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).map a) = limMap (Functor.whiskerRight a H) := sorry

/-- Presented identity pro-morphisms realize as identity module maps. -/
theorem map_id (A : PNatInverseSystem C) :
    map H (𝟙 ((@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A)) = 𝟙 (limit (A ⋙ H)) := sorry

/-- Realization preserves composition of actual pro-morphisms. -/
theorem map_comp {A B D : PNatInverseSystem C}
    (f : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B)
    (g : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B ⟶ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj D) :
    map H (f ≫ g) = map H f ≫ map H g := sorry

/-- A specified pro-isomorphism induces a module-limit isomorphism through
the realized forward and inverse morphisms. -/
def mapIso {A B : PNatInverseSystem C}
    (e : (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj A ≅ (@Pro.lim C _ (OrderDual ℕ+) _ _ _ _).obj B) :
    limit (A ⋙ H) ≅ limit (B ⋙ H) where
  hom := map H e.hom
  inv := map H e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

end CategoryTheory.Pro.ModuleLimit
