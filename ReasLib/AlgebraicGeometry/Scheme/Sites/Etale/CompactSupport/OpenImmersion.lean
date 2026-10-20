module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion

/-!
# Covariance of compactly supported global étale sections along open immersions

For a separated scheme `X` locally of finite type over a field `k` and an abelian
étale sheaf `F`, an open immersion `j : X' ⟶ X` over `k` induces an injective
additive map `H^0_c(X', F|_{X'}) →+ H^0_c(X, F)` by unique extension of properly
supported sections as in `extendSupportedAlongOpen`. These maps assemble into a
covariant functor on Zariski opens of `X`.
-/

public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k]

/-- The morphism of small étale identity objects `X'_étale ⟶ X_étale` induced by
an open immersion over `k`. -/
def globalEtaleOpenImmersion {X X' : SchemeOverField k} (j : X' ⟶ X)
    [IsOpenImmersion j.left] :
    (etaleRestriction j.left).obj (globalEtale X'.left) ⟶ globalEtale X.left :=
  MorphismProperty.Over.homMk j.left

/-- The reduced closed-subscheme structure on the support of a compactly
supported global section of `F|_{X'}`. -/
private def globalCompactSupportSectionStructure {X X' : SchemeOverField k}
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    ClosedSubschemeStructure
      (abelianSheafSectionSupport
        ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)
        (globalEtale X'.left)
        ((globalSectionsCompactSupportSubgroup X'
            ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ)) :=
  ClosedSubschemeStructure.reduced _

/-- The reduced support of a compactly supported global section is a closed
immersion into `X'`. -/
private theorem isClosedImmersion_globalCompactSupportSectionStructure_ι
    {X X' : SchemeOverField k} [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom]
    (j : X' ⟶ X) [IsOpenImmersion j.left]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    IsClosedImmersion (globalCompactSupportSectionStructure j F σ).ι :=
  inferInstanceAs
    (IsClosedImmersion (globalCompactSupportSectionStructure j F σ).ideal.subschemeι)

/-- The support of a compactly supported global section of `F|_{X'}` remains a
closed immersion after composing with `j.left`. -/
private theorem isClosedImmersion_support_globalOpenImmersion {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    IsClosedImmersion
      ((globalCompactSupportSectionStructure j F σ).ι ≫
        (globalEtaleOpenImmersion j).left) :=
  sorry

/-- A compactly supported global section of `F|_{X'}` is supported in the image
of its reduced support subscheme, as a section of `F` on the image of `X'` in
`X.Etale`. -/
private theorem globalCompactSupportSections_mem_supportedIn {X X' : SchemeOverField k}
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    ((globalSectionsCompactSupportSubgroup X'
          ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ) ∈
      abelianSheafSectionsSupportedIn F
        ((etaleRestriction j.left).obj (globalEtale X'.left))
        (Set.range (globalCompactSupportSectionStructure j F σ).ι) :=
  sorry

/-- The unique extension of a compactly supported global section of `F|_{X'}` to
a global section of `F` on `X`, via `extendSupportedAlongOpen`. -/
def extendGlobalCompactSupportSection {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    F.obj.obj (op (globalEtale X.left)) :=
  (@extendSupportedAlongOpen _ F _ _ (globalEtaleOpenImmersion j) _
      (globalCompactSupportSectionStructure j F σ).ι
      (isClosedImmersion_globalCompactSupportSectionStructure_ι j F σ)
      (isClosedImmersion_support_globalOpenImmersion j F σ)
      ⟨(globalSectionsCompactSupportSubgroup X'
            ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ,
        globalCompactSupportSections_mem_supportedIn j F σ⟩).val

/-- The unique extension of a compactly supported global section along an open
immersion still has compact support. -/
theorem hasCompactSupport_extendGlobalCompactSupportSection {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    HasCompactSupport F (extendGlobalCompactSupportSection j F σ) :=
  sorry

/-- Extension by zero sends the zero compactly supported section to zero. -/
private theorem extendGlobalCompactSupportSection_zero {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    extendGlobalCompactSupportSection j F 0 = 0 := by
  sorry

/-- Extension by zero preserves addition of compactly supported sections. -/
private theorem extendGlobalCompactSupportSection_add {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ τ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    extendGlobalCompactSupportSection j F (σ + τ) =
      extendGlobalCompactSupportSection j F σ + extendGlobalCompactSupportSection j F τ := by
  sorry

/-- Canonical covariance `H^0_c(X', F|_{X'}) →+ H^0_c(X, F)` along an open
immersion of separated locally finite-type `k`-schemes. -/
@[expose] def globalSectionsCompactSupportOpenImmersion {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportSubgroup X'
        ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup X F where
  toFun σ :=
    ⟨extendGlobalCompactSupportSection j F σ,
      (mem_globalSectionsCompactSupportSubgroup_iff X F
          (extendGlobalCompactSupportSection j F σ)).mpr
        (hasCompactSupport_extendGlobalCompactSupportSection j F σ)⟩
  map_zero' := by exact Subtype.ext (extendGlobalCompactSupportSection_zero j F)
  map_add' := by
    intro σ τ
    exact Subtype.ext (extendGlobalCompactSupportSection_add j F σ τ)

/-- The covariance map acts by unique extension of properly supported sections. -/
theorem globalSectionsCompactSupportOpenImmersion_apply {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    (globalSectionsCompactSupportOpenImmersion j F σ).val =
      extendGlobalCompactSupportSection j F σ :=
  rfl

/-- The covariance map `H^0_c(X', F|_{X'}) ⟶ H^0_c(X, F)` is injective. -/
theorem globalSectionsCompactSupportOpenImmersion_injective {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective (globalSectionsCompactSupportOpenImmersion j F) :=
  sorry

/-- Restriction of the extended global section along the open immersion recovers
the original compactly supported section. -/
theorem globalSectionsCompactSupportOpenImmersion_restrict {X X' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] (j : X' ⟶ X)
    [IsOpenImmersion j.left] (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X'
      ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)) :
    F.obj.map (globalEtaleOpenImmersion j).op
        (extendGlobalCompactSupportSection j F σ) =
      (globalSectionsCompactSupportSubgroup X'
          ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).subtype σ :=
  sorry

/-- Covariance along the identity open immersion is the identity. -/
theorem globalSectionsCompactSupportOpenImmersion_id (X : SchemeOverField k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportOpenImmersion (𝟙 X) F =
      AddMonoidHom.id (globalSectionsCompactSupportSubgroup X F) :=
  sorry

/-- Restriction of abelian small-étale sheaves along equal étale morphisms is
isomorphic. -/
private def etaleRestrictionSheafCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [Etale f] [Etale g] (e : f = g) :
    etaleRestrictionSheaf f AddCommGrpCat.{u} ≅
      etaleRestrictionSheaf g AddCommGrpCat.{u} :=
  eqToIso (e ▸ rfl)

/-- The underlying scheme morphism of a composite open immersion over `k` is an
open immersion. -/
instance isOpenImmersion_comp_over_left {X X' X'' : SchemeOverField k}
    (j : X' ⟶ X) (j' : X'' ⟶ X')
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] :
    IsOpenImmersion (j' ≫ j).left :=
  inferInstanceAs (IsOpenImmersion (j'.left ≫ j.left))

/-- Covariance along nested open immersions `X'' ⟶ X' ⟶ X` is the composite of
the two covariance maps, after identifying the two-step restriction of `F` with
restriction along the composite. -/
theorem globalSectionsCompactSupportOpenImmersion_comp {X X' X'' : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom]
    [IsSeparated X''.hom] [LocallyOfFiniteType X''.hom]
    (j : X' ⟶ X) (j' : X'' ⟶ X') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (globalSectionsCompactSupportOpenImmersion j F).comp
        ((globalSectionsCompactSupportOpenImmersion j'
            ((etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj F)).comp
          (globalSectionsCompactSupportMapIso X''
            ((etaleAbelianRestrictionSheafCompIso j.left j'.left).symm.app F))) =
      globalSectionsCompactSupportOpenImmersion (j' ≫ j) F :=
  sorry

/-- Restriction of `F` to `U` identifies with restriction to `V` followed by
restriction along `X.homOfLE h`. -/
def etaleRestrictionSheaf_opensLe {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {U V : X.Opens} (h : U ≤ V) :
    (etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F ≅
      (etaleRestrictionSheaf (X.homOfLE h) AddCommGrpCat.{u}).obj
        ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F) :=
  (etaleRestrictionSheafCongr (X.homOfLE_ι h).symm).app F ≪≫
    (etaleAbelianRestrictionSheafCompIso V.ι (X.homOfLE h)).symm.app F

/-- Covariance of compactly supported global sections along an inclusion of
Zariski opens of `X`. -/
def globalSectionsCompactSupportOpensHom {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) {U V : X.left.Opens}
    (h : U ≤ V) :
    globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X V)
        ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F) :=
  (globalSectionsCompactSupportOpenImmersion (SchemeOverField.restrictOpenHom X h)
      ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F)).comp
    (globalSectionsCompactSupportMapIso (SchemeOverField.restrictOpen X U)
      (etaleRestrictionSheaf_opensLe F h))

/-- Covariance of compactly supported global sections along the open immersion of
a Zariski open subscheme of `X`. -/
abbrev globalSectionsCompactSupportOpens {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (U : X.left.Opens) :
    globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) →+
      globalSectionsCompactSupportSubgroup X F :=
  globalSectionsCompactSupportOpenImmersion (SchemeOverField.restrictOpenι X U) F

/-- Covariance for the identity inclusion of a Zariski open is the identity. -/
private theorem globalSectionsCompactSupportOpensHom_id {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (U : X.left.Opens) :
    globalSectionsCompactSupportOpensHom F (show U ≤ U from le_rfl) =
      AddMonoidHom.id (globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F)) := by
  sorry

/-- Covariance for a composite inclusion of Zariski opens is the composite map. -/
private theorem globalSectionsCompactSupportOpensHom_comp {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    {U V W : X.left.Opens} (h : U ≤ V) (h' : V ≤ W) :
    globalSectionsCompactSupportOpensHom F (h.trans h') =
      (globalSectionsCompactSupportOpensHom F h').comp
        (globalSectionsCompactSupportOpensHom F h) := by
  sorry

/-- The assignment `U ↦ H^0_c(U, F|_U)` on Zariski opens of `X`, with covariance
maps along open inclusions, as a covariant functor to abelian groups. -/
def globalSectionsCompactSupportCopresheaf {X : SchemeOverField k}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    X.left.Opens ⥤ AddCommGrpCat.{u} where
  obj U :=
    AddCommGrpCat.of
      (globalSectionsCompactSupportSubgroup (SchemeOverField.restrictOpen X U)
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F))
  map {_ _} h :=
    AddCommGrpCat.ofHom (globalSectionsCompactSupportOpensHom F (leOfHom h))
  map_id U := congrArg AddCommGrpCat.ofHom (globalSectionsCompactSupportOpensHom_id F U)
  map_comp f g := congrArg AddCommGrpCat.ofHom
    (globalSectionsCompactSupportOpensHom_comp F (leOfHom f) (leOfHom g))

end AlgebraicGeometry.Scheme.Etale

end
