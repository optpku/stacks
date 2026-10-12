/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor algebras of module sheaves on ringed sites

This file sheafifies the sectionwise tensor-algebra functor over an arbitrary commutative
ringed site.  The construction, its action on morphisms, and its degree-one inclusion live at
this topology-independent layer; ringed spaces and schemes are thin specializations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.TensorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The sectionwise tensor-algebra presheaf underlying a module sheaf. -/
noncomputable abbrev presheaf (F : ringedSiteModuleCategory J 𝒪) :
    PresheafOfModules (ringSheaf J 𝒪).obj :=
  PresheafOfModules.TensorAlgebra.presheaf 𝒪.obj F.val

/-- The morphism of sectionwise tensor-algebra presheaves induced by a module-sheaf
morphism. -/
noncomputable abbrev presheafMap {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    presheaf 𝒪 F ⟶ presheaf 𝒪 G :=
  PresheafOfModules.TensorAlgebra.hom 𝒪.obj f.val

/-- The degree-one inclusion into the sectionwise tensor-algebra presheaf. -/
noncomputable abbrev presheafι (F : ringedSiteModuleCategory J 𝒪) :
    F.val ⟶ presheaf 𝒪 F :=
  PresheafOfModules.TensorAlgebra.ι 𝒪.obj F.val

/-- The tensor-algebra functor on module sheaves over a commutative ringed site. -/
noncomputable def functor :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.forget (ringSheaf J 𝒪) ⋙
    PresheafOfModules.TensorAlgebra.functor 𝒪.obj ⋙
    moduleSheafification 𝒪

/-- Section 17.21 (01CF): the underlying module sheaf of the tensor algebra on a commutative
ringed site. -/
@[stacks 01CF "tensor algebra on a ringed site"]
noncomputable abbrev sheaf (F : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 :=
  (functor 𝒪).obj F

/-- The morphism on tensor-algebra sheaves induced by a module-sheaf morphism. -/
noncomputable abbrev map {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    sheaf 𝒪 F ⟶ sheaf 𝒪 G :=
  (functor 𝒪).map f

/-- On underlying presheaves, the tensor-algebra sheaf map is the sheafification of the
sectionwise tensor-algebra map. -/
theorem map_eq_sheafification {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    map 𝒪 f = (moduleSheafification 𝒪).map (presheafMap 𝒪 f) := sorry

/-- The degree-one inclusion from a module sheaf to its tensor-algebra sheaf. -/
noncomputable def ι (F : ringedSiteModuleCategory J 𝒪) : F ⟶ sheaf 𝒪 F :=
  (moduleSheafificationValIso 𝒪 F).inv ≫
    (moduleSheafification 𝒪).map (presheafι 𝒪 F)

/-- The degree-one inclusions into tensor-algebra sheaves are natural in the module sheaf. -/
theorem ι_naturality {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    f ≫ ι 𝒪 G = ι 𝒪 F ≫ map 𝒪 f := sorry

/-- The degree-one inclusions satisfy the naturality equation in functorial form. -/
theorem unit_naturality (F G : ringedSiteModuleCategory J 𝒪) (f : F ⟶ G) :
    (𝟭 _).map f ≫ ι 𝒪 G = ι 𝒪 F ≫ (functor 𝒪).map f := sorry

/-- The canonical degree-one inclusion into the tensor-algebra functor on module sheaves. -/
noncomputable def unit : 𝟭 _ ⟶ functor 𝒪 where
  app F := ι 𝒪 F
  naturality := fun {F G} f ↦ unit_naturality 𝒪 F G f

end SheafOfModules.RingedSite.TensorAlgebra
