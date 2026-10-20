module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal pullback of module sheaves on ringed spaces

The explicit `CoreMonoidal` boundary specializes the commutative ringed-site pullback owner to a
ringed-space morphism. Inverse image of opens is representably flat, which also supplies the
canonical monoidal pullback structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/- The explicit core is the ringed-space specialization of the ringed-site owner. -/
/-- The presheaf-level core consumed by the ringed-space pullback constructors. -/
@[stacks 01CD "explicit monoidal pullback core"]
abbrev presheafCore (f : X ⟶ Y) :=
  SheafOfModules.Pullback.presheafCore.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (O := Y.sheaf) (O' := X.sheaf)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)

/-- The explicit strong-monoidal core for module pullback on ringed spaces. -/
@[stacks 01CD "explicit monoidal pullback core"]
noncomputable def pullbackCoreMonoidalOf
    (m : presheafCore f) :
    (pullback f).CoreMonoidal :=
  SheafOfModules.Pullback.coreMonoidalOf.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (O := Y.sheaf) (O' := X.sheaf)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)
    m

/-- The class-shaped strong-monoidal structure obtained from the explicit pullback core. -/
@[stacks 01CD "explicit monoidal pullback structure", implicit_reducible]
noncomputable def pullbackMonoidalOf (m : presheafCore f) :
    (pullback f).Monoidal :=
  (pullbackCoreMonoidalOf f m).toMonoidal

/-- The unit isomorphism obtained from the explicit pullback core. -/
@[stacks 01CD "explicit pullback unit isomorphism"]
noncomputable def pullbackUnitIsoOf (m : presheafCore f) :
    (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  SheafOfModules.Pullback.unitIsoOf.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (O := Y.sheaf) (O' := X.sheaf)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)
    m

/-- The forward unit comparison obtained from the explicit pullback core. -/
@[stacks 01CD "explicit pullback unit comparison"]
noncomputable abbrev pullbackUnitComparisonOf (m : presheafCore f) :
    (pullback f).obj (𝟙_ Y.Modules) ⟶ 𝟙_ X.Modules :=
  (pullbackUnitIsoOf f m).hom

/-- The tensor natural isomorphism obtained from the explicit pullback core. -/
@[stacks 01CD "explicit pullback tensor comparison"]
noncomputable def pullbackTensorNatIsoOf (m : presheafCore f) :
    MonoidalCategory.tensor Y.Modules ⋙ pullback f ≅
      Functor.prod (pullback f) (pullback f) ⋙ MonoidalCategory.tensor X.Modules :=
  SheafOfModules.Pullback.tensorNatIsoOf.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (O := Y.sheaf) (O' := X.sheaf)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)
    m

/-- The objectwise tensor isomorphism obtained from the explicit pullback core. -/
@[stacks 01CD "explicit pullback tensor isomorphism"]
noncomputable def pullbackTensorIsoOf (m : presheafCore f) (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ≅ (pullback f).obj M ⊗ (pullback f).obj N :=
  SheafOfModules.Pullback.tensorIsoOf.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (O := Y.sheaf) (O' := X.sheaf)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)
    m M N

/-- The forward tensor comparison obtained from the explicit pullback core. -/
@[stacks 01CD "explicit pullback tensor comparison morphism"]
noncomputable abbrev pullbackTensorComparisonOf (m : presheafCore f) (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ⟶ (pullback f).obj M ⊗ (pullback f).obj N :=
  (pullbackTensorIsoOf f m M N).hom

/-- The component of the named tensor natural isomorphism is the named objectwise isomorphism. -/
@[simp, stacks 01CD "pullback tensor comparison component"]
theorem pullbackTensorNatIsoOf_app (m : presheafCore f) (M N : Y.Modules) :
    (pullbackTensorNatIsoOf f m).app (M, N) = pullbackTensorIsoOf f m M N := sorry

section Compatibility

/-- The canonical presheaf core assembled from representable flatness. -/
@[stacks 01CD "representably flat ringed-space presheaf core"]
noncomputable def presheafCoreMonoidal : presheafCore f :=
  SheafOfModules.Pullback.Construction.presheafCoreMonoidal.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (O := Y.sheaf) (O' := X.sheaf)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)

/-- The canonical strong-monoidal core for ringed-space pullback. -/
@[stacks 01CD "representably flat ringed-space pullback core"]
noncomputable def pullbackCoreMonoidal : (pullback f).CoreMonoidal :=
  SheafOfModules.Pullback.coreMonoidal.{u, u, u, u, u}
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (O := Y.sheaf) (O' := X.sheaf)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)

/-- Pullback of module sheaves along a morphism of a ringed space is canonically strong monoidal. -/
@[stacks 01CD "monoidal module pullback", implicit_reducible]
noncomputable instance pullbackMonoidal :
    (pullback f).Monoidal :=
  (pullbackCoreMonoidal f).toMonoidal

/-- Pullback identifies the structure module with the structure module. -/
@[stacks 01CD "pullback of the tensor unit"]
noncomputable abbrev pullbackUnitIso :
    (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  pullbackUnitIsoOf f (presheafCoreMonoidal f)

/-- The natural tensor comparison isomorphism for pullback of module sheaves on ringed spaces. -/
@[stacks 01CD "natural pullback-tensor comparison"]
noncomputable abbrev pullbackTensorNatIso :
    MonoidalCategory.tensor Y.Modules ⋙ pullback f ≅
      Functor.prod (pullback f) (pullback f) ⋙ MonoidalCategory.tensor X.Modules :=
  pullbackTensorNatIsoOf f (presheafCoreMonoidal f)

/-- Pullback commutes with tensor products of module sheaves. -/
@[stacks 01CD "pullback-tensor comparison"]
noncomputable abbrev pullbackTensorIso (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ≅ (pullback f).obj M ⊗ (pullback f).obj N :=
  pullbackTensorIsoOf f (presheafCoreMonoidal f) M N

/-- The forward morphism of the pullback-tensor comparison. -/
@[stacks 01CD "pullback-tensor comparison morphism"]
noncomputable abbrev pullbackTensorComparison (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ⟶ (pullback f).obj M ⊗ (pullback f).obj N :=
  (pullbackTensorIso f M N).hom

end Compatibility

end AlgebraicGeometry.RingedSpace.Hom
