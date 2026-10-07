module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import stacks_project.Chap92.«92_25_1_1_Site»

/-!
# Structure sheaves and morphisms of ringed topoi on `C_{X/Λ}`

This leaf owns the sheaves `O : (U ⟶ A) ↦ Γ(A, O_A)` and
`underline{O}_X = π⁻¹ O_X : (U ⟶ A) ↦ O_X(U)`, together with the morphisms of
ringed topoi `i` (identity on topoi) and `π` induced by `u : C_{X/Λ} ⥤ X_Zar`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- The scheme-valued realization sending `(U ⟶ A)` to the affine space `A`. -/
def affineRealization : Obj Λ X ⥤ Scheme.{u} where
  obj P := P.A
  map {P Q} f := (f : Hom P Q).right
  map_id := sorry
  map_comp := sorry

/-- Identity morphisms of `C_{X/Λ}` act as identities on affine spaces. -/
theorem affineRealization_map_id (P : Obj Λ X) :
    (affineRealization Λ X).map (𝟙 P) = 𝟙 P.A :=
  sorry

/-- Composition of morphisms of `C_{X/Λ}` is composition of affine-space maps. -/
theorem affineRealization_map_comp {P Q R : Obj Λ X} (f : P ⟶ Q) (g : Q ⟶ R) :
    (affineRealization Λ X).map (f ≫ g) =
      (affineRealization Λ X).map f ≫ (affineRealization Λ X).map g :=
  sorry

/-- The global-sections presheaf `(U ⟶ A) ↦ Γ(A, O_A)` is a sheaf on `C_{X/Λ}`. -/
theorem structurePresheaf_isSheaf :
    Presheaf.IsSheaf (topology Λ X)
      (Scheme.Site.structurePresheaf (affineRealization Λ X)) :=
  sorry

/-- The structure sheaf `O` on `C_{X/Λ}`, sending `(U ⟶ A)` to `Γ(A, O_A)`. -/
def structureSheaf : Sheaf (topology Λ X) RingCat.{u} :=
  ⟨Scheme.Site.structurePresheaf (affineRealization Λ X), structurePresheaf_isSheaf Λ X⟩

/-- The value of `O` at `(U ⟶ A)` is the global-sections ring of `A`. -/
theorem structureSheaf_obj (P : Obj Λ X) :
    (structureSheaf Λ X).obj.obj (op P) = RingCat.of Γ(P.A, ⊤) :=
  sorry

/-- The inverse-image presheaf `π⁻¹ O_X`, sending `(U ⟶ A)` to `O_X(U)`. -/
def inverseImageStructurePresheaf : (Obj Λ X)ᵒᵖ ⥤ RingCat.{u} :=
  (forgetZariski Λ X).op ⋙ (Zariski.Small.structureSheaf X).obj

/-- The inverse-image presheaf `π⁻¹ O_X` is a sheaf on `C_{X/Λ}`. -/
theorem inverseImageStructurePresheaf_isSheaf :
    Presheaf.IsSheaf (topology Λ X) (inverseImageStructurePresheaf Λ X) :=
  sorry

/-- The sheaf `underline{O}_X = π⁻¹ O_X` on `C_{X/Λ}`. -/
def inverseImageStructureSheaf : Sheaf (topology Λ X) RingCat.{u} :=
  ⟨inverseImageStructurePresheaf Λ X, inverseImageStructurePresheaf_isSheaf Λ X⟩

/-- The value of `underline{O}_X` at `(U ⟶ A)` is the value of `O_X` at `U`. -/
theorem inverseImageStructureSheaf_obj (P : Obj Λ X) :
    (inverseImageStructureSheaf Λ X).obj.obj (op P) =
      (Zariski.Small.structureSheaf X).obj.obj (op P.U) :=
  sorry

/-- Components of `i♯` are the maps `Γ(A, O_A) ⟶ Γ(U, O_U)` induced by `U ⟶ A`. -/
theorem structureSheafMap_naturality {P Q : (Obj Λ X)ᵒᵖ} (f : P ⟶ Q) :
    (structureSheaf Λ X).obj.map f ≫
        (forget₂ CommRingCat RingCat).map Q.unop.hom.appTop =
      (forget₂ CommRingCat RingCat).map P.unop.hom.appTop ≫
        (inverseImageStructureSheaf Λ X).obj.map f :=
  sorry

/-- The obvious sheaf map `i♯ : O ⟶ underline{O}_X`. -/
def structureSheafMap : structureSheaf Λ X ⟶ inverseImageStructureSheaf Λ X where
  hom :=
    { app P := (forget₂ CommRingCat RingCat).map P.unop.hom.appTop
      naturality := fun _ _ _ ↦ sorry }

/-- The component of `i♯` at `(U ⟶ A)` is `A ⟶ U` on global sections. -/
theorem structureSheafMap_app (P : Obj Λ X) :
    (structureSheafMap Λ X).hom.app (op P) =
      (forget₂ CommRingCat RingCat).map P.hom.appTop :=
  sorry

/-- The ringed site `(Sh(C_{X/Λ}), O)`. -/
abbrev ringedSite : RingedSite.{u + 1, u, u} :=
  ofRingSheaf (topology Λ X) (structureSheaf Λ X)

/-- The ringed site `(Sh(C_{X/Λ}), underline{O}_X)`. -/
abbrev inverseImageRingedSite : RingedSite.{u + 1, u, u} :=
  ofRingSheaf (topology Λ X) (inverseImageStructureSheaf Λ X)

/-- The same-site morphism of ringed sites with identity base functor and
structure map `i♯`. -/
def sameSite : inverseImageRingedSite Λ X ⟶ ringedSite Λ X :=
  SameSite.hom (structureSheafMap Λ X)

/-- The base functor of `i` is the identity of `C_{X/Λ}`. -/
theorem i_base : (sameSite Λ X).base = 𝟭 (Obj Λ X) :=
  sorry

/-- Inverse image of `O_X` along `u` recovers `underline{O}_X`. -/
theorem toZariski_inverseImage :
    (forgetZariski Λ X).op ⋙ (Zariski.Small.structureSheaf X).obj =
      (inverseImageStructureSheaf Λ X).obj :=
  sorry

/-- The identity-on-topoi comparison identifying `π⁻¹ O_X` with `underline{O}_X`. -/
def toZariskiStructureMap :
    (forgetZariski Λ X).op ⋙ (Zariski.Small.ringedSite X).structureSheaf.obj ⟶
      (inverseImageRingedSite Λ X).structureSheaf.obj where
  app _ := 𝟙 _
  naturality := sorry

/-- The inherited topology on `C_{X/Λ}` admits sheaf composition with `forget RingCat`. -/
instance topology_hasSheafCompose :
    (topology Λ X).HasSheafCompose (CategoryTheory.forget RingCat.{u}) :=
  sorry

/-- The morphism of ringed topoi `i : (Sh(C_{X/Λ}), underline{O}_X) ⟶ (Sh(C_{X/Λ}), O)`,
identity on underlying topoi, with `i♯ : O ⟶ underline{O}_X` the obvious map. -/
def i [(topology Λ X).HasSheafCompose (CategoryTheory.forget RingCat.{u})] :
    ToposHom (inverseImageRingedSite Λ X) (ringedSite Λ X) where
  toTopos := MorphismOfTopoiIn.id (topology Λ X)
  structureMap :=
    (MorphismOfTopoiIn.ringInverseImageIdIso).hom.app (structureSheaf Λ X) ≫
      structureSheafMap Λ X

/-- The small Zariski topology of `X` admits sheaf composition with `forget RingCat`. -/
instance smallZariski_hasSheafCompose :
    X.smallZariskiTopology.HasSheafCompose (CategoryTheory.forget RingCat.{u}) :=
  sorry

/-- Type-valued sheafification exists on the inherited topology of `C_{X/Λ}`. -/
instance topology_hasSheafify : HasSheafify (topology Λ X) (Type u) :=
  sorry

/-- Pointwise right Kan extensions along `uᵒᵖ` exist for type-valued presheaves. -/
instance forgetZariski_op_hasPointwiseRightKanExtension
    (P : (Obj Λ X)ᵒᵖ ⥤ Type u) :
    (forgetZariski Λ X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The underlying morphism of topoi of `π`, induced by the cocontinuous functor `u`. -/
def toZariskiToTopos :
    MorphismOfTopoiIn X.smallZariskiTopology (topology Λ X) :=
  (forgetZariski Λ X).morphismOfTopoiInOfCocontinuous
    (topology Λ X) X.smallZariskiTopology

/-- The forgetful functor `u` as a functor of underlying categories of ringed sites. -/
def forgetZariskiRinged :
    inverseImageRingedSite Λ X ⥤ Zariski.Small.ringedSite X :=
  forgetZariski Λ X

/-- The forgetful functor of ringed sites is cocontinuous. -/
instance forgetZariskiRinged_isCocontinuous :
    (forgetZariskiRinged Λ X).IsCocontinuous
      (inverseImageRingedSite Λ X).siteTopology
      (Zariski.Small.ringedSite X).siteTopology :=
  sorry

/-- Sheafification of type-valued presheaves on the ringed site `(Sh(C), underline{O}_X)`. -/
instance inverseImageRingedSite_hasSheafify :
    HasSheafify (inverseImageRingedSite Λ X).siteTopology (Type u) :=
  sorry

/-- Pointwise right Kan extensions along `uᵒᵖ` as a functor of ringed sites. -/
instance forgetZariskiRinged_op_hasPointwiseRightKanExtension
    (P : (inverseImageRingedSite Λ X)ᵒᵖ ⥤ Type u) :
    (forgetZariskiRinged Λ X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The inverse-image structure map of `π`, identifying `π⁻¹ O_X` with `underline{O}_X`. -/
def toZariskiStructureSheafMap :
    (toZariskiToTopos Λ X).ringInverseImage.obj
        (Zariski.Small.ringedSite X).structureSheaf ⟶
      (inverseImageRingedSite Λ X).structureSheaf :=
  Cocontinuous.structureMap.{u + 1, u, u + 1, u, u}
    (forgetZariskiRinged Λ X) (toZariskiStructureMap Λ X)

/-- The morphism of ringed topoi `π : (Sh(C_{X/Λ}), underline{O}_X) ⟶ (Sh(X_Zar), O_X)`
induced by the forgetful functor `u : C_{X/Λ} ⥤ X_Zar`. -/
def toZariski : ToposHom (inverseImageRingedSite Λ X) (Zariski.Small.ringedSite X) where
  toTopos := toZariskiToTopos Λ X
  structureMap := toZariskiStructureSheafMap Λ X

end AlgebraicGeometry.Scheme.CotangentSite
