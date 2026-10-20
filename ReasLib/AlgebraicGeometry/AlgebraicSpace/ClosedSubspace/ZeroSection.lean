module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Section
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal

/-!
# Zero schemes of sections of invertible modules on algebraic spaces

The closed subspace `Z(s) ⊂ X` cut out by a global section of an invertible
`𝒪_X`-module is defined by the image of the dual-section map `ℒ^{⊗ -1} ⟶ 𝒪_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.isInvertibleObject
  (inverse inverseTensorIso)
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dual of a global section `s` of an invertible module, as the morphism
`ℒ^{⊗ -1} ⟶ 𝒪_X` obtained by whiskering `regularSectionHom` with the chosen
tensor inverse and applying `inverseTensorIso`. -/
noncomputable def dualSectionHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    inverse ℒ ⟶ SheafOfModules.unit (structureSheaf X) :=
  (ρ_ (inverse ℒ)).inv ≫
    (inverse ℒ ◁ ((Modules.structureModuleIsoTensorUnit X).inv ≫
      regularSectionHom ℒ s)) ≫
    (inverseTensorIso ℒ).hom ≫
    (Modules.structureModuleIsoTensorUnit X).inv

/-- The dual-section morphism is the dual of `regularSectionHom` via
`inverseTensorIso` and the structure-module comparison with the tensor unit. -/
theorem dualSectionHom_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    dualSectionHom ℒ s =
      (ρ_ (inverse ℒ)).inv ≫
        (inverse ℒ ◁ ((Modules.structureModuleIsoTensorUnit X).inv ≫
          regularSectionHom ℒ s)) ≫
        (inverseTensorIso ℒ).hom ≫
        (Modules.structureModuleIsoTensorUnit X).inv :=
  sorry

/-- The quasi-coherent ideal sheaf of `Z(s)`, as the image of
`s : ℒ^{⊗ -1} ⟶ 𝒪_X`. -/
noncomputable def zeroIdealSubobject {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) : IdealSubobject X :=
  imageSubobject (dualSectionHom ℒ s)

/-- The zero ideal of a section is the image subobject of the dual-section
morphism. -/
theorem zeroIdealSubobject_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    zeroIdealSubobject ℒ s = imageSubobject (dualSectionHom ℒ s) :=
  sorry

/-- The image of the dual-section morphism is a quasi-coherent ideal sheaf. -/
instance instIsQuasiCoherent_zeroIdealSubobject {S : Scheme.{u}}
    {X : AlgebraicSpace S} (ℒ : X.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) : IsQuasiCoherent (zeroIdealSubobject ℒ s) :=
  sorry

/-- The zero scheme `Z(s)` of a global section of an invertible `𝒪_X`-module,
as the closed subspace cut out by the image of `s : ℒ^{⊗ -1} ⟶ 𝒪_X`. -/
noncomputable def zeroScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (zeroIdealSubobject ℒ s)

/-- The zero scheme is the closed subspace attached to the image of the
dual-section morphism. -/
theorem zeroScheme_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    zeroScheme ℒ s =
      ClosedSubspace.ofQuasiCoherentIdeal (zeroIdealSubobject ℒ s) :=
  sorry

/-- The canonical closed immersion `Z(s) ⟶ X`. -/
noncomputable abbrev zeroSchemeι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    (zeroScheme ℒ s).X ⟶ X :=
  (zeroScheme ℒ s).ι

/-- The inclusion of `Z(s)` is the closed immersion cut out by the image
ideal. -/
theorem zeroSchemeι_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    zeroSchemeι ℒ s = subschemeι (zeroIdealSubobject ℒ s) :=
  sorry

/-- The ideal sheaf of `Z(s)` recovers the image of `s : ℒ^{⊗ -1} ⟶ 𝒪_X`. -/
theorem zeroScheme_idealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (ℒ : X.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    (zeroScheme ℒ s).idealSheaf = zeroIdealSubobject ℒ s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
