module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Restriction
public import ReasLib.CategoryTheory.Sites.Simplicial.Stage
public import ReasLib.CategoryTheory.Sites.Simplicial.Total

/-!
# Stage inclusions of a ringed simplicial site

The total ringed site `(Sh(C_total), O)`, the degree-`n` ringed site `(Sh(C_n), O_n)`
with `O_n` the continuous inverse image of `O` along `ofStage`, the flat morphism of
ringed topoi `g_n`, and the component `a_n = a ∘ g_n` of an augmentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w uD vD

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsSiteDiagram C J]

variable (O : Sheaf (topology C J) RingCat.{w})

/-- The total ringed site `(Sh(C_total), O)`. -/
abbrev totalRingedSite : RingedSite.{u, v, w} :=
  ofRingSheaf (topology C J) O

/-- The structure sheaf of `totalRingedSite C J O` is `O`. -/
theorem totalRingedSite_structureSheaf :
    (totalRingedSite C J O).structureSheaf = O :=
  rfl

/-- The ring sheaf `O_n` on `C.obj n`, the continuous inverse image of `O` along
`ofStage C n`. -/
abbrev componentRingSheaf (n : SimplexCategory) : Sheaf (J n).toGrothendieck RingCat.{w} :=
  Cocontinuous.inverseImageRingSheaf (ofStage C n) O

/-- `componentRingSheaf` is inverse image of `O` along `ofStage C n`. -/
theorem componentRingSheaf_eq (n : SimplexCategory) :
    componentRingSheaf C J O n = Cocontinuous.inverseImageRingSheaf (ofStage C n) O :=
  rfl

/-- The degree-`n` ringed site `(Sh(C_n), O_n)`. -/
abbrev componentRingedSite (n : SimplexCategory) : RingedSite.{u, v, w} :=
  ofRingSheaf (J n).toGrothendieck (componentRingSheaf C J O n)

/-- The structure sheaf of `componentRingedSite C J O n` is `O_n`. -/
theorem componentRingedSite_structureSheaf (n : SimplexCategory) :
    (componentRingedSite C J O n).structureSheaf = componentRingSheaf C J O n :=
  rfl

variable [UnivLE.{max u v, w}]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

/-- The identity comparison `(ofStage C n).op ⋙ O ⟶ componentRingSheaf C J O n`
from which the structure map of `g_n` is obtained, so `g_n⁻¹ O = O_n`. -/
def stageIdentityComparison (n : SimplexCategory) :
    (ofStage C n).op ⋙ (totalRingedSite C J O).structureSheaf.obj ⟶
      (componentRingedSite C J O n).structureSheaf.obj :=
  𝟙 ((ofStage C n).op ⋙ O.obj)

/-- `stageIdentityComparison` is the identity on the restricted structure sheaf. -/
theorem stageIdentityComparison_eq_id (n : SimplexCategory) :
    stageIdentityComparison C J O n = 𝟙 ((ofStage C n).op ⋙ O.obj) :=
  rfl

/-- The morphism of ringed topoi `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` induced by
the continuous and cocontinuous inclusion `ofStage C n`, with identity structure map
so that `g_n⁻¹ O = O_n`. -/
def stageMorphism (n : SimplexCategory) :
    ToposHom (componentRingedSite C J O n) (totalRingedSite C J O) :=
  Cocontinuous.restrictionMorphism (totalRingedSite C J O)
    (J n).toGrothendieck (ofStage C n)

/-- The stage inclusion `g_n` is flat: its structure map is the identity comparison,
and identity structure maps are flat. -/
theorem stageMorphism_isFlat (n : SimplexCategory)
    [(SheafOfModules.restrictScalars.{w}
        (stageMorphism C J O n).structureMap).IsRightAdjoint] :
    ToposHom.IsFlat (stageMorphism C J O n) :=
  sorry

variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- The component morphism `a_n = a ∘ g_n` of an augmentation of ringed topoi. -/
def augmentationComponent (a : ToposHom (totalRingedSite C J O) D) (n : SimplexCategory) :
    ToposHom (componentRingedSite C J O n) D :=
  (stageMorphism C J O n).comp a

/-- `augmentationComponent a n` is the composite `g_n` then `a`. -/
theorem augmentationComponent_comp (a : ToposHom (totalRingedSite C J O) D)
    (n : SimplexCategory) :
    augmentationComponent C J O a n = (stageMorphism C J O n).comp a :=
  rfl

/-- Flatness of an augmentation implies flatness of each component `a ∘ g_n`. -/
theorem augmentationComponent_isFlat (a : ToposHom (totalRingedSite C J O) D)
    [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
    [∀ n, (SheafOfModules.restrictScalars.{w}
        (augmentationComponent C J O a n).structureMap).IsRightAdjoint]
    [∀ n, (SheafOfModules.restrictScalars.{w}
        (stageMorphism C J O n).structureMap).IsRightAdjoint]
    [ToposHom.IsFlat a] (n : SimplexCategory) :
    ToposHom.IsFlat (augmentationComponent C J O a n) :=
  sorry

/-- Flatness of every component `a ∘ g_n` implies flatness of the augmentation. -/
theorem isFlat_of_forall_augmentationComponent (a : ToposHom (totalRingedSite C J O) D)
    [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
    [∀ n, (SheafOfModules.restrictScalars.{w}
        (augmentationComponent C J O a n).structureMap).IsRightAdjoint]
    (h : ∀ n : SimplexCategory, ToposHom.IsFlat (augmentationComponent C J O a n)) :
    ToposHom.IsFlat a :=
  sorry

/-- A morphism from a ringed simplicial total site is flat if and only if every
canonical stage component is flat. -/
theorem augmentation_isFlat_iff (a : ToposHom (totalRingedSite C J O) D)
    [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
    [∀ n, (SheafOfModules.restrictScalars.{w}
      (augmentationComponent C J O a n).structureMap).IsRightAdjoint] :
    ToposHom.IsFlat a ↔
      ∀ n : SimplexCategory, ToposHom.IsFlat (augmentationComponent C J O a n) :=
  sorry

end CategoryTheory.SimplicialSites
