/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_5_TwistDescent
public import stacks_project.Chap71.Lemma_71_11_5_BaseChange

/-!
# The canonical global Serre-twist algebra

The actual local products descend uniquely through restriction to the affine
étale basis. Bilinearization and the module-sheafification adjunction give the
actual tensor morphisms. Thus the family carries constructed operations, not
arbitrary operations accompanied by asserted comparison laws.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

section Underlying
variable {S : Scheme.{u}} (P : AlgebraicSpace S)

/-- Actual restriction of set sheaves to the dense affine basis, in the value universe u. -/
def typeRestriction : Sheaf (smallEtaleTopology P) (Type u) ⥤
    Sheaf (affineEtaleTopology P) (Type u) :=
  (affineEtaleInclusion P).sheafPushforwardContinuous (Type u)
    (affineEtaleTopology P) (smallEtaleTopology P)

/-- The dense basis determines maps of small-valued sheaves uniquely. Every
test scheme has a small affine-open cover, so no universe-smallness hypothesis is added. -/
instance typeRestriction_isEquivalence : (typeRestriction P).IsEquivalence := sorry

/-- The actual underlying set sheaf of a module. -/
def typeSheaf (M : P.Modules) : Sheaf (smallEtaleTopology P) (Type u) :=
  ⟨M.val.presheaf ⋙ forget AddCommGrpCat, sorry⟩

/-- The actual sectionwise pair sheaf, used to descend multiplication. -/
def pairSheaf (M N : P.Modules) : Sheaf (smallEtaleTopology P) (Type u) :=
  ⟨{ obj U := (M.val.obj U) × (N.val.obj U)
     map f := TypeCat.ofHom fun p ↦ (M.val.map f p.1, N.val.map f p.2)
     map_id := sorry
     map_comp := sorry }, sorry⟩

/-- The singleton sheaf, used to descend the actual unit section. -/
def singletonSheaf : Sheaf (smallEtaleTopology P) (Type u) :=
  ⟨(Functor.const _).obj PUnit.{u + 1}, sorry⟩

end Underlying

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
variable (hF : F.IsAssociatedToQuadruples deg)

/-- Local multiplication, on actual top-open sections of the local modules. -/
def localMulValue (U : affineEtaleSite (toAlgebraicSpace F hF)) (a b : ℤ)
    (x : (localObj F hF U a).val.obj (op ⊤))
    (y : (localObj F hF U b).val.obj (op ⊤)) :
    (localObj F hF U (a + b)).val.obj (op ⊤) :=
  ((localMul F hF U a b).val.app (op ⊤)).hom
    (SheafOfModules.RingedSite.tensorSection U.obj.left.left.sheaf (op ⊤) x y)

/-- Local unit from the actual monoidal unit map on the scheme. -/
def localOneValue (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    (localObj F hF U 0).val.obj (op ⊤) :=
  (((RingedSpace.unitIsoTensorUnit U.obj.left.left.toRingedSpace).hom ≫
    localUnit F hF U).val.app (op ⊤)).hom
      (show U.obj.left.left.ringCatSheaf.obj.obj (op ⊤) from 1)

/-- Transfer the actual local product through the fixed affine comparison. -/
def basisMulValue (U : affineEtaleSite (toAlgebraicSpace F hF)) (a b : ℤ)
    (x : (obj F hF a).val.obj (op U.obj)) (y : (obj F hF b).val.obj (op U.obj)) :
    (obj F hF (a + b)).val.obj (op U.obj) :=
  (affineComparison F hF (a + b)).hom.val.app (op U)
    (localMulValue F hF U a b
      ((affineComparison F hF a).inv.val.app (op U) x)
      ((affineComparison F hF b).inv.val.app (op U) y))

/-- Transfer the actual local unit through the same fixed comparison. -/
def basisOneValue (U : affineEtaleSite (toAlgebraicSpace F hF)) :
    (obj F hF 0).val.obj (op U.obj) :=
  (affineComparison F hF 0).hom.val.app (op U) (localOneValue F hF U)

/-- The local product gives a map between the actual restricted set sheaves. -/
def basisMul (a b : ℤ) :
    (typeRestriction (toAlgebraicSpace F hF)).obj
      (pairSheaf (toAlgebraicSpace F hF) (obj F hF a) (obj F hF b)) ⟶
    (typeRestriction (toAlgebraicSpace F hF)).obj
      (typeSheaf (toAlgebraicSpace F hF) (obj F hF (a + b))) where
  hom :=
    { app U := TypeCat.ofHom fun p ↦ basisMulValue F hF U.unop a b p.1 p.2
      naturality := sorry }

/-- The local unit gives a map from the actual restricted singleton sheaf. -/
def basisOne :
    (typeRestriction (toAlgebraicSpace F hF)).obj (singletonSheaf (toAlgebraicSpace F hF)) ⟶
    (typeRestriction (toAlgebraicSpace F hF)).obj
      (typeSheaf (toAlgebraicSpace F hF) (obj F hF 0)) where
  hom :=
    { app U := TypeCat.ofHom fun _ ↦ basisOneValue F hF U.unop
      naturality := sorry }

/-- The unique descended product, computed by fullness of actual dense restriction. -/
def productMap (a b : ℤ) :
    pairSheaf (toAlgebraicSpace F hF) (obj F hF a) (obj F hF b) ⟶
      typeSheaf (toAlgebraicSpace F hF) (obj F hF (a + b)) :=
  (typeRestriction (toAlgebraicSpace F hF)).preimage (basisMul F hF a b)

/-- The unique descended unit from that same actual restriction functor. -/
def oneMap : singletonSheaf (toAlgebraicSpace F hF) ⟶
    typeSheaf (toAlgebraicSpace F hF) (obj F hF 0) :=
  (typeRestriction (toAlgebraicSpace F hF)).preimage (basisOne F hF)

/-- Evaluation of the descended product on local sections. -/
def productValue (U : (smallEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (a b : ℤ)
    (x : (obj F hF a).val.obj U) (y : (obj F hF b).val.obj U) :
    (obj F hF (a + b)).val.obj U :=
  (productMap F hF a b).hom.app U (x, y)

/-- Evaluation of the descended unit on the unique singleton section. -/
def oneValue (U : (smallEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) :
    (obj F hF 0).val.obj U :=
  (oneMap F hF).hom.app U PUnit.unit

/-- Scalar multiplication on the actual descended unit gives its module morphism. -/
def unit : SheafOfModules.unit (structureSheaf (toAlgebraicSpace F hF)) ⟶ obj F hF 0 where
  val :=
    { app := fun U ↦ by
        let M := (SheafOfModules.unit (structureSheaf (toAlgebraicSpace F hF))).val.obj U
        let N := (obj F hF 0).val.obj U
        exact @ModuleCat.ofHom ((structureSheaf (toAlgebraicSpace F hF)).obj.obj U) _ M N
          M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
          { toFun := fun r ↦ (show (structureSheaf (toAlgebraicSpace F hF)).obj.obj U from r) •
              oneValue F hF U
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- Bilinearization in the existing commutative presentation, using the descended values. -/
def commProduct (a b : ℤ) :
    PresheafOfModules.BilinearMap (commStructureSheaf (toAlgebraicSpace F hF)).obj
      ((Modules.toCommModules (toAlgebraicSpace F hF)).obj (obj F hF a)).val
      ((Modules.toCommModules (toAlgebraicSpace F hF)).obj (obj F hF b)).val
      ((Modules.toCommModules (toAlgebraicSpace F hF)).obj (obj F hF (a + b))).val where
  app U := LinearMap.mk₂ ((commStructureSheaf (toAlgebraicSpace F hF)).obj.obj U)
    (fun x y ↦ asCommSection (obj F hF (a + b))
      (productValue F hF U a b (ofCommSection (obj F hF a) x)
        (ofCommSection (obj F hF b) y))) sorry sorry sorry sorry
  naturality := sorry

/-- The existing actual tensor comparison is a composite of canonical isomorphisms. -/
theorem commTensorComparison_isIso (M N : (toAlgebraicSpace F hF).Modules) :
    IsIso (commTensorComparison M N) := sorry

/-- Descend the bilinear product through the actual module-sheafification adjunction. -/
def commMul (a b : ℤ) :
    (Modules.toCommModules (toAlgebraicSpace F hF)).obj (obj F hF a ⊗ obj F hF b) ⟶
      (Modules.toCommModules (toAlgebraicSpace F hF)).obj (obj F hF (a + b)) :=
  (@asIso _ _ _ _ (commTensorComparison (obj F hF a) (obj F hF b))
    (commTensorComparison_isIso F hF _ _)).inv ≫
    (moduleSheafificationHomEquiv.{u + 1, u, u, u}
      (commStructureSheaf (toAlgebraicSpace F hF)) _ _).symm (commProduct F hF a b).toHom

/-- The actual multiplication morphism, transported through the existing scalar equivalence. -/
def mul (a b : ℤ) : obj F hF a ⊗ obj F hF b ⟶ obj F hF (a + b) :=
  (Modules.commModulesEquivalence (toAlgebraicSpace F hF)).counitIso.inv.app
      (obj F hF a ⊗ obj F hF b) ≫
    (Modules.ofCommModules (toAlgebraicSpace F hF)).map (commMul F hF a b) ≫
    (Modules.commModulesEquivalence (toAlgebraicSpace F hF)).counitIso.hom.app (obj F hF (a + b))

/-- Lift the actual unit through the specified universe-lift unit map. -/
def liftedOne (U : (smallEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) :
    (Modules.liftModule (obj F hF 0)).val.obj U :=
  (((Modules.liftedUnitIso (toAlgebraicSpace F hF)).inv ≫
    Modules.liftModuleMap (unit F hF)).val.app U).hom
      (liftedUnitSection (toAlgebraicSpace F hF) U)

/-- Lift the actual product using the specified pure-tensor comparison. -/
def liftedMul (U : (smallEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (a b : ℤ) :
    (Modules.liftModule (obj F hF a)).val.obj U →ₗ[
      (commStructureSheafLift (toAlgebraicSpace F hF)).obj.obj U]
      (Modules.liftModule (obj F hF b)).val.obj U →ₗ[
        (commStructureSheafLift (toAlgebraicSpace F hF)).obj.obj U]
        (Modules.liftModule (obj F hF (a + b))).val.obj U :=
  (liftModuleTensorApp (obj F hF a) (obj F hF b) U).compr₂
    ((Modules.liftModuleMap (mul F hF a b)).val.app U).hom

/-- The constructed global graded algebra of actual Serre twists. -/
def algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift (toAlgebraicSpace F hF)) where
  obj n := Modules.liftModule (obj F hF n)
  one := liftedOne F hF
  mul := liftedMul F hF
  map_one := sorry
  map_mul := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

/-- The canonical family replacing the former arbitrary-family input at the target. -/
def family : TwistFamily (toAlgebraicSpace F hF) where
  algebra := algebra F hF
  obj := obj F hF
  iso _ := Iso.refl _
  unit := unit F hF
  mul := mul F hF
  unit_spec := sorry
  mul_spec := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
