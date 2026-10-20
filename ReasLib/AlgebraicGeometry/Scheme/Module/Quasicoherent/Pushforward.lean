/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.Coherence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Additive
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition.Coherence
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Identity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherence of pushforwards
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {X S : Scheme.{u}}

/-- The object-property premise that a scheme morphism preserves quasi-coherent modules. -/
@[stacks 01LC "quasi-coherent pushforward preservation premise"]
abbrev preservesQuasiCoherent (f : X ⟶ S) : Prop :=
  quasiCoherentModuleProperty X ≤
    (quasiCoherentModuleProperty S).inverseImage (Scheme.Modules.pushforward f)

/-- Restrict scheme-theoretic module pushforward to quasi-coherent modules from a
map between the corresponding object properties. -/
@[stacks 01LC "pushforward restricted to quasi-coherent modules"]
noncomputable def pushforwardOf
    (f : X ⟶ S)
    (hpush : preservesQuasiCoherent f) :
    QCoh X ⥤ QCoh S :=
  FullSubcategory.restrict (Scheme.Modules.pushforward f) hpush

/-- Restricting module pushforward to quasi-coherent modules preserves additivity. -/
@[stacks 01LC "additivity of restricted quasicoherent pushforward", instance]
instance pushforwardOf.additive
    (f : X ⟶ S) (hpush : preservesQuasiCoherent f) :
    (pushforwardOf f hpush).Additive := sorry

namespace pushforwardOf

/-- Forgetting quasi-coherence after `pushforwardOf` recovers ordinary module
pushforward. -/
@[stacks 01LC "pushforward restriction inclusion comparison"]
noncomputable def inclusionIso
    (f : X ⟶ S)
    (hpush : preservesQuasiCoherent f) :
    pushforwardOf f hpush ⋙ inclusion S ≅
      inclusion X ⋙ Scheme.Modules.pushforward f :=
  FullSubcategory.restrict.compιIso (Scheme.Modules.pushforward f) hpush

end pushforwardOf

namespace pushforward

/-- Qcqs pushforward carries quasicoherent modules to quasicoherent modules. -/
@[stacks 01LC "quasicoherent pushforward maps objects"]
theorem mapsTo (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    preservesQuasiCoherent f := sorry

end pushforward

/-- Pushforward along a qcqs morphism, restricted to quasicoherent modules. -/
@[stacks 01LC "quasicoherent pushforward functor"]
noncomputable def pushforward (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    QCoh X ⥤ QCoh S :=
  pushforwardOf f (pushforward.mapsTo f)

/-- Pushforward along a qcqs morphism is additive on quasi-coherent modules. -/
@[stacks 01LC "additivity of quasicoherent pushforward", instance]
instance pushforward.additive
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (pushforward f).Additive := sorry

/-- Forgetting quasicoherence after restricted pushforward recovers ambient
module-sheaf pushforward. -/
@[stacks 01LC "quasicoherent pushforward inclusion comparison"]
noncomputable def pushforward.inclusionIso
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    pushforward f ⋙ inclusion S ≅
      inclusion X ⋙ Scheme.Modules.pushforward f :=
  pushforwardOf.inclusionIso f (pushforward.mapsTo f)

namespace pushforward

/-- The underlying module sheaf of quasicoherent pushforward is ambient
module-sheaf pushforward. -/
@[simp, stacks 01LC "quasicoherent pushforward object readout"]
theorem obj_obj (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : QCoh X) :
    ((pushforward f).obj F).obj =
      (Scheme.Modules.pushforward f).obj F.obj := sorry

/-- The underlying morphism of quasicoherent pushforward is the ambient
pushforward of the underlying morphism. -/
@[simp, stacks 01LC "quasicoherent pushforward morphism readout"]
theorem map_hom (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {F G : QCoh X} (phi : F ⟶ G) :
    ((pushforward f).map phi).hom =
      (Scheme.Modules.pushforward f).map phi.hom := sorry

/-- Pushforward along the identity is canonically isomorphic to the identity
on quasicoherent modules. -/
@[stacks 01LC "identity comparison for quasicoherent pushforward"]
noncomputable def idIso (X : Scheme.{u}) :
    pushforward (𝟙 X) ≅ 𝟭 (QCoh X) :=
  FullSubcategory.restrict.natIso
      (pushforward.mapsTo (𝟙 X))
      (FullSubcategory.restrict.mapsToId (quasiCoherentModuleProperty X))
      (Scheme.Modules.pushforwardId X) ≪≫
    FullSubcategory.restrict.idIso (quasiCoherentModuleProperty X)

/-- Composing quasicoherent pushforwards agrees canonically with pushforward
along the composite morphism. -/
@[stacks 01LC "composition comparison for quasicoherent pushforward"]
noncomputable def compIso {Y : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  (FullSubcategory.restrict.compIso
      (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward g)
      (pushforward.mapsTo f) (pushforward.mapsTo g)).symm ≪≫
    FullSubcategory.restrict.natIso
      (FullSubcategory.restrict.mapsToComp
        (pushforward.mapsTo f) (pushforward.mapsTo g))
      (pushforward.mapsTo (f ≫ g))
      (Scheme.Modules.pushforwardComp f g)

/-- Pushforward along equal scheme morphisms has a canonical comparison on
quasi-coherent modules.  Both sets of qc/qs instances are part of the two restricted functors'
types; the equality identifies their underlying scheme morphisms. -/
@[stacks 01LC "equal-morphism comparison for quasicoherent pushforward"]
noncomputable def congrIso {f g : X ⟶ S} (h : f = g)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] :
    pushforward f ≅ pushforward g :=
  FullSubcategory.restrict.natIso
    (pushforward.mapsTo f) (pushforward.mapsTo g)
    (Scheme.Modules.pushforwardCongr h)

end pushforward

namespace pushforward.idIso

/-- The underlying forward component of identity pushforward is the ambient
identity-pushforward comparison. -/
@[simp, stacks 01LC "identity pushforward forward component"]
theorem hom_app_hom (X : Scheme.{u}) (F : QCoh X) :
    ((pushforward.idIso X).hom.app F).hom =
      (Scheme.Modules.pushforwardId X).hom.app F.obj := sorry

/-- The underlying inverse component of identity pushforward is the ambient
identity-pushforward comparison. -/
@[simp, stacks 01LC "identity pushforward inverse component"]
theorem inv_app_hom (X : Scheme.{u}) (F : QCoh X) :
    ((pushforward.idIso X).inv.app F).hom =
      (Scheme.Modules.pushforwardId X).inv.app F.obj := sorry

end pushforward.idIso

namespace pushforward.congrIso

/-- The underlying forward component of the equal-morphism comparison. -/
@[simp, stacks 01LC "equal-morphism pushforward forward component"]
theorem hom_app_hom {f g : X ⟶ S} (h : f = g)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (F : QCoh X) :
    ((pushforward.congrIso h).hom.app F).hom =
      (Scheme.Modules.pushforwardCongr h).hom.app F.obj := sorry

/-- The underlying inverse component of the equal-morphism comparison. -/
@[simp, stacks 01LC "equal-morphism pushforward inverse component"]
theorem inv_app_hom {f g : X ⟶ S} (h : f = g)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (F : QCoh X) :
    ((pushforward.congrIso h).inv.app F).hom =
      (Scheme.Modules.pushforwardCongr h).inv.app F.obj := sorry

end pushforward.congrIso

namespace pushforward.compIso

/-- The underlying forward component of composite pushforward is the ambient
pushforward-composition comparison. -/
@[simp, stacks 01LC "composite pushforward forward component"]
theorem hom_app_hom {Y : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (F : QCoh X) :
    ((pushforward.compIso f g).hom.app F).hom =
      (Scheme.Modules.pushforwardComp f g).hom.app F.obj := sorry

/-- The underlying inverse component of composite pushforward is the ambient
pushforward-composition comparison. -/
@[simp, stacks 01LC "composite pushforward inverse component"]
theorem inv_app_hom {Y : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (F : QCoh X) :
    ((pushforward.compIso f g).inv.app F).hom =
      (Scheme.Modules.pushforwardComp f g).inv.app F.obj := sorry

/-- The composition comparisons satisfy associativity after the canonical
transport across categorical reassociation. -/
@[stacks 01LC "quasicoherent pushforward associativity"]
theorem associativity {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact h] [QuasiSeparated h] :
    Functor.isoWhiskerRight (pushforward.compIso f g) (pushforward h) ≪≫
        pushforward.compIso (f ≫ g) h ≪≫
        pushforward.congrIso (Category.assoc f g h) =
      Functor.associator (pushforward f) (pushforward g) (pushforward h) ≪≫
        Functor.isoWhiskerLeft (pushforward f) (pushforward.compIso g h) ≪≫
        pushforward.compIso f (g ≫ h) := sorry

/-- The composition comparison satisfies the left identity law. -/
@[stacks 01LC "quasicoherent pushforward left identity"]
theorem left_unit (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    pushforward.compIso (𝟙 X) f ≪≫
        pushforward.congrIso (Category.id_comp f) =
      Functor.isoWhiskerRight (pushforward.idIso X) (pushforward f) ≪≫
        Functor.leftUnitor (pushforward f) := sorry

/-- The composition comparison satisfies the right identity law. -/
@[stacks 01LC "quasicoherent pushforward right identity"]
theorem right_unit (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    pushforward.compIso f (𝟙 Y) ≪≫
        pushforward.congrIso (Category.comp_id f) =
      Functor.isoWhiskerLeft (pushforward f) (pushforward.idIso Y) ≪≫
        Functor.rightUnitor (pushforward f) := sorry

end pushforward.compIso

namespace pushforward.inclusionIso

/-- The forward inclusion comparison for quasicoherent pushforward is
componentwise the identity. -/
@[simp, stacks 01LC "pushforward inclusion forward component"]
theorem hom_app (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : QCoh X) :
    (pushforward.inclusionIso f).hom.app F =
      𝟙 ((Scheme.Modules.pushforward f).obj F.obj) := sorry

/-- The inverse inclusion comparison for quasicoherent pushforward is
componentwise the identity. -/
@[simp, stacks 01LC "pushforward inclusion inverse component"]
theorem inv_app (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : QCoh X) :
    (pushforward.inclusionIso f).inv.app F =
      𝟙 ((Scheme.Modules.pushforward f).obj F.obj) := sorry

end pushforward.inclusionIso

end AlgebraicGeometry.Scheme.QCoh

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

namespace pushforward

/-- Pushforward along a quasi-compact and quasi-separated scheme morphism preserves
quasi-coherent modules. -/
@[stacks 01LC, instance]
instance isQuasicoherent
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).IsQuasicoherent := sorry

/-- Explicit-hypothesis form of qcqs pushforward preserving
quasi-coherence. -/
@[stacks 01LC]
theorem isQuasicoherentOf
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {F : X.Modules} (hF : F.IsQuasicoherent) :
    ((pushforward f).obj F).IsQuasicoherent := sorry

end pushforward

end AlgebraicGeometry.Scheme.Modules
