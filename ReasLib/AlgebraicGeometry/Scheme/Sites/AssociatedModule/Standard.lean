/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheafification

/-!
# Associated modules on the standard scheme sites

This module bundles the pullback-sections presheaf on the five standard big sites and
on the small Zariski and small étale sites of a scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Abelian-group-valued sheafification exists on every slice of a canonical big
standard site. -/
theorem instHasWeakSheafifyBigOver (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : Over S,
      HasWeakSheafify ((τ.overTopology S).over U) AddCommGrpCat.{u} :=
  AlgebraicGeometry.StandardTopology.Big.over_hasWeakSheafify τ S

/-- Abelian-group-valued sheafification exists on every slice of a canonical small
Zariski or small étale site. -/
instance instHasWeakSheafifySmallOver (σ : SmallStandardTopology) (S : Scheme.{u}) :
    ∀ U : σ.site S,
      HasWeakSheafify ((σ.topology S).over U) AddCommGrpCat.{u} := by
  cases σ
  · exact AlgebraicGeometry.Scheme.Zariski.Small.over_hasWeakSheafify S
  · exact AlgebraicGeometry.Scheme.Etale.Small.over_hasWeakSheafify S

/-- Sheafification equivalences on slices of a canonical big standard site are exactly
the locally bijective morphisms. -/
theorem instWEqualsLocallyBijectiveBigOver (τ : StandardTopology) (S : Scheme.{u}) :
    ∀ U : Over S,
      ((τ.overTopology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.StandardTopology.Big.over_wEqualsLocallyBijective τ S

/-- Sheafification equivalences on slices of a canonical small Zariski or small étale
site are exactly the locally bijective morphisms. -/
instance instWEqualsLocallyBijectiveSmallOver
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    ∀ U : σ.site S,
      ((σ.topology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  cases σ
  · exact AlgebraicGeometry.Scheme.Zariski.Small.over_wEqualsLocallyBijective S
  · exact AlgebraicGeometry.Scheme.Etale.Small.over_wEqualsLocallyBijective S

/-- The global-functions presheaf on schemes over `S`. -/
abbrev structurePresheaf (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ RingCat.{u} :=
  Scheme.Over.structurePresheaf (𝟭 (Over S))

/-- The global-functions presheaf is obtained from the identity functor on `Over S`. -/
theorem structurePresheaf_spec (S : Scheme.{u}) :
    structurePresheaf S = Scheme.Over.structurePresheaf (𝟭 (Over S)) := rfl

/-- The pullback-sections module presheaf on schemes over `S`. -/
noncomputable abbrev presheaf (S : Scheme.{u}) (F : S.Modules) :
    _root_.PresheafOfModules (structurePresheaf S) :=
  Scheme.Modules.pullbackSectionsPresheaf (𝟭 (Over S)) F

/-- The underlying additive presheaf is the canonical pullback-sections presheaf. -/
theorem presheaf_spec (S : Scheme.{u}) (F : S.Modules) :
    presheaf S F = Scheme.Modules.pullbackSectionsPresheaf (𝟭 (Over S)) F := rfl

/-- The global-functions presheaf is a sheaf on every standard big site of `S`. -/
theorem bigStructurePresheaf_isSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (τ.overTopology S) (structurePresheaf S) :=
  AlgebraicGeometry.StandardTopology.Big.structurePresheaf_isSheaf τ S

/-- The structure sheaf on the standard big `τ`-site of `S`. -/
noncomputable def bigStructureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (τ.overTopology S) RingCat.{u} :=
  ⟨structurePresheaf S, bigStructurePresheaf_isSheaf τ S⟩

/-- The underlying presheaf of the big structure sheaf is the global-functions
presheaf. -/
theorem bigStructureSheaf_spec (τ : StandardTopology) (S : Scheme.{u}) :
    (bigStructureSheaf τ S).obj = structurePresheaf S := rfl

/-- Pullback sections of a quasi-coherent module form a sheaf on every standard big site. -/
theorem presheaf_isSheaf (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (τ.overTopology S) (presheaf S F).presheaf :=
  AlgebraicGeometry.StandardTopology.Big.pullbackSectionsPresheaf_isSheaf τ S F

/-- The module sheaf on the standard big `τ`-site associated to `F`. -/
noncomputable def big (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] : SheafOfModules (bigStructureSheaf τ S) :=
  ⟨presheaf S F, presheaf_isSheaf τ S F⟩

/-- The underlying module presheaf of `big τ S F` is the pullback-sections presheaf. -/
theorem big_spec (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (big τ S F).val = presheaf S F := rfl

/-- The global-functions presheaf on the selected canonical small site of `S`. -/
abbrev smallStructurePresheaf (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (σ.site S)ᵒᵖ ⥤ RingCat.{u} :=
  Scheme.Over.structurePresheaf (σ.toOver S)

/-- The selected small structure presheaf is obtained from the canonical forgetful
functor to `Over S`. -/
theorem smallStructurePresheaf_spec (σ : SmallStandardTopology) (S : Scheme.{u}) :
    smallStructurePresheaf σ S = Scheme.Over.structurePresheaf (σ.toOver S) := rfl

/-- The pullback-sections module presheaf on the selected canonical small site. -/
noncomputable abbrev smallPresheaf (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) : _root_.PresheafOfModules (smallStructurePresheaf σ S) :=
  Scheme.Modules.pullbackSectionsPresheaf (σ.toOver S) F

/-- The selected small module presheaf is the canonical pullback-sections presheaf. -/
theorem smallPresheaf_spec (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) :
    smallPresheaf σ S F = Scheme.Modules.pullbackSectionsPresheaf (σ.toOver S) F := rfl

/-- The global-functions presheaf is a sheaf on the selected canonical small site. -/
theorem smallStructurePresheaf_isSheaf (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (σ.topology S) (smallStructurePresheaf σ S) := by
  cases σ
  · exact AlgebraicGeometry.Scheme.Zariski.Small.structurePresheaf_isSheaf S
  · exact AlgebraicGeometry.Scheme.Etale.Small.structurePresheaf_isSheaf S

/-- The structure sheaf on the selected canonical small site of `S`. -/
noncomputable def smallStructureSheaf (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Sheaf (σ.topology S) RingCat.{u} :=
  ⟨smallStructurePresheaf σ S, smallStructurePresheaf_isSheaf σ S⟩

/-- The underlying presheaf of the selected small structure sheaf is the global-functions
presheaf. -/
theorem smallStructureSheaf_spec (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (smallStructureSheaf σ S).obj = smallStructurePresheaf σ S := rfl

/-- Pullback sections of a quasi-coherent module form a sheaf on the selected canonical
small site. -/
theorem smallPresheaf_isSheaf (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (σ.topology S) (smallPresheaf σ S F).presheaf := by
  cases σ
  · exact AlgebraicGeometry.Scheme.Zariski.Small.pullbackSectionsPresheaf_isSheaf S F
  · exact AlgebraicGeometry.Scheme.Etale.Small.pullbackSectionsPresheaf_isSheaf S F

/-- The module sheaf on the selected canonical small site associated to `F`. -/
noncomputable def small (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] : SheafOfModules (smallStructureSheaf σ S) :=
  ⟨smallPresheaf σ S F, smallPresheaf_isSheaf σ S F⟩

/-- The underlying module presheaf of `small σ S F` is the restriction of the
pullback-sections presheaf to the selected canonical small site. -/
theorem small_spec (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (small σ S F).val = smallPresheaf σ S F := rfl

end AlgebraicGeometry.Scheme.AssociatedModule
