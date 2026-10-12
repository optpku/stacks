/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.LeftTensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinant subobjects on commutative ringed sites

For a module sheaf `F`, degree-one multiplication gives
`Λ(F) ⟶ F ⟶[Mod] Λ(F)` after currying.  Its kernel subobject is the determinant.  Keeping the
subobject as the canonical owner records its embedding into the exterior algebra and makes the
construction reusable outside ringed spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Determinant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The action of degree-one elements on the exterior-algebra sheaf, curried as
`Λ(F) ⟶ F ⟶[Mod] Λ(F)`. -/
@[stacks 0FJN "determinant action"]
noncomputable def action
    (F : ringedSiteModuleCategory J 𝒪) :
    ExteriorAlgebra.sheaf 𝒪 F ⟶
      InternalHom.obj 𝒪 F (ExteriorAlgebra.sheaf 𝒪 F) :=
  InternalHom.homEquiv 𝒪 F (ExteriorAlgebra.sheaf 𝒪 F)
    (ExteriorAlgebra.sheaf 𝒪 F) (ExteriorAlgebra.leftTensorMap 𝒪 F)

/-- The determinant of `F` as the kernel subobject of its degree-one action on `Λ(F)`. -/
@[stacks 0FJN "determinant subobject"]
noncomputable abbrev subobject
    (F : ringedSiteModuleCategory J 𝒪) :
    Subobject (ExteriorAlgebra.sheaf 𝒪 F) :=
  kernelSubobject (action F)

/-- The module sheaf underlying the determinant subobject. -/
@[stacks 0FJN "determinant module sheaf"]
noncomputable abbrev sheaf
    (F : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 :=
  subobject F

/-- Scoped notation for the determinant module sheaf on a commutative ringed site. -/
scoped[SheafOfModules.RingedSite.Determinant] notation:max "det(" F ")" =>
  _root_.SheafOfModules.RingedSite.Determinant.sheaf F

/-- The canonical inclusion of the determinant into the exterior-algebra sheaf. -/
@[stacks 0FJN "determinant inclusion"]
noncomputable abbrev ι
    (F : ringedSiteModuleCategory J 𝒪) :
    sheaf F ⟶ ExteriorAlgebra.sheaf 𝒪 F :=
  (subobject F).arrow

/-- The determinant inclusion is annihilated by the degree-one action. -/
@[reassoc, stacks 0FJN "determinant kernel equation"]
theorem ι_comp_action
    (F : ringedSiteModuleCategory J 𝒪) :
    ι F ≫ action F = 0 := sorry

/-- A morphism into the exterior-algebra sheaf factors through the determinant exactly when it
is annihilated by the degree-one action. -/
@[stacks 0FJN "universal property of the determinant subobject"]
theorem factors_iff
    (F : ringedSiteModuleCategory J 𝒪)
    {K : ringedSiteModuleCategory J 𝒪}
    (f : K ⟶ ExteriorAlgebra.sheaf 𝒪 F) :
    (subobject F).Factors f ↔ f ≫ action F = 0 := sorry

/-- The canonical lift of a morphism annihilated by the degree-one action to the determinant
sheaf. -/
@[stacks 0FJN "lift to the determinant sheaf"]
noncomputable def lift
    (F : ringedSiteModuleCategory J 𝒪)
    {K : ringedSiteModuleCategory J 𝒪}
    (f : K ⟶ ExteriorAlgebra.sheaf 𝒪 F) (h : f ≫ action F = 0) :
    K ⟶ sheaf F :=
  factorThruKernelSubobject (action F) f h

/-- The canonical lift to the determinant recovers the original morphism after the determinant
inclusion. -/
@[reassoc, stacks 0FJN "determinant lift equation"]
theorem lift_ι
    (F : ringedSiteModuleCategory J 𝒪)
    {K : ringedSiteModuleCategory J 𝒪}
    (f : K ⟶ ExteriorAlgebra.sheaf 𝒪 F) (h : f ≫ action F = 0) :
    lift F f h ≫ ι F = f := sorry

/-- Morphisms into the determinant are determined by their composites with its canonical
inclusion. -/
@[ext, stacks 0FJN "determinant morphism extensionality"]
theorem hom_ext
    (F : ringedSiteModuleCategory J 𝒪)
    {K : ringedSiteModuleCategory J 𝒪}
    {f g : K ⟶ sheaf F} (h : f ≫ ι F = g ≫ ι F) :
    f = g := sorry

/-- The image of the determinant inclusion under an exterior-algebra isomorphism is annihilated
by the target degree-one action. -/
@[reassoc, stacks 0FJN "determinant isomorphism factorization"]
theorem mapIsoHom_comp_action
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    (ι F ≫ ExteriorAlgebra.map 𝒪 e.hom) ≫ action G = 0 := sorry

/-- The forward morphism on determinant sheaves induced by a module-sheaf isomorphism. -/
@[stacks 0FJN "forward morphism on determinant sheaves"]
noncomputable def mapIsoHom
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    sheaf F ⟶ sheaf G :=
  lift G (ι F ≫ ExteriorAlgebra.map 𝒪 e.hom) (mapIsoHom_comp_action e)

/-- The forward determinant morphism is characterized by the induced exterior-algebra map. -/
@[reassoc, stacks 0FJN "forward determinant morphism inclusion equation"]
theorem mapIsoHom_ι
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    mapIsoHom e ≫ ι G = ι F ≫ ExteriorAlgebra.map 𝒪 e.hom := sorry

/-- The inverse morphism on determinant sheaves induced by a module-sheaf isomorphism. -/
@[stacks 0FJN "inverse morphism on determinant sheaves"]
noncomputable def mapIsoInv
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    sheaf G ⟶ sheaf F :=
  mapIsoHom e.symm

/-- The inverse determinant morphism is characterized by the inverse exterior-algebra map. -/
@[reassoc, stacks 0FJN "inverse determinant morphism inclusion equation"]
theorem mapIsoInv_ι
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    mapIsoInv e ≫ ι F = ι G ≫ ExteriorAlgebra.map 𝒪 e.inv := sorry

/-- The forward and inverse determinant morphisms compose to the identity. -/
theorem mapIsoHom_mapIsoInv
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    mapIsoHom e ≫ mapIsoInv e = 𝟙 _ := sorry

/-- The inverse and forward determinant morphisms compose to the identity. -/
theorem mapIsoInv_mapIsoHom
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    mapIsoInv e ≫ mapIsoHom e = 𝟙 _ := sorry

/-- A module-sheaf isomorphism induces a canonical isomorphism of determinant sheaves. -/
@[stacks 0FJN "determinant isomorphism induced by a module-sheaf isomorphism"]
noncomputable def mapIso
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    sheaf F ≅ sheaf G where
  hom := mapIsoHom e
  inv := mapIsoInv e
  hom_inv_id := mapIsoHom_mapIsoInv e
  inv_hom_id := mapIsoInv_mapIsoHom e

/-- The forward map of the determinant isomorphism is the canonical determinant lift. -/
@[simp]
theorem mapIso_hom
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    (mapIso e).hom = mapIsoHom e := sorry

/-- The inverse map of the determinant isomorphism is the lift induced by the inverse
module-sheaf isomorphism. -/
@[simp]
theorem mapIso_inv
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    (mapIso e).inv = mapIsoInv e := sorry

/-- The determinant isomorphism commutes with the canonical inclusions into exterior algebras. -/
@[reassoc, stacks 0FJN "determinant isomorphism inclusion equation"]
theorem mapIso_hom_ι
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) :
    (mapIso e).hom ≫ ι G = ι F ≫ ExteriorAlgebra.map 𝒪 e.hom := sorry

/-- The identity module-sheaf isomorphism induces the identity determinant isomorphism. -/
@[simp]
theorem mapIso_refl (F : ringedSiteModuleCategory J 𝒪) :
    mapIso (Iso.refl F) = Iso.refl (sheaf F) := sorry

/-- Determinant isomorphisms respect composition of module-sheaf isomorphisms. -/
@[simp]
theorem mapIso_trans
    {F G H : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) (e' : G ≅ H) :
    mapIso (e.trans e') = (mapIso e).trans (mapIso e') := sorry

end SheafOfModules.RingedSite.Determinant
