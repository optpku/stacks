module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.PointQuotient

/-!
# Reconstruct algebra maps by actual atlas-section gluing

A descended point has its concrete atlas pullback and spectrum lift. Pull the
atlas's actual algebra map back along that lift. On each direct-image scheme
chart, its section maps glue over the native pullback of the atlas cover. The
canonical direct-image cone lift then assembles the global algebra map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The actual base arrow of the point's supplied atlas pullback. -/
def relativeSpectrumPointLocalBase (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    ofOver (relativeSpectrumPointAtlasOver A p) ⟶ X :=
  ofOverMap (relativeSpectrumPointAtlasToTest A p) ≫ relativeSpectrumPointBase A p

/-- Pulling the constructed atlas algebra map along the point's actual atlas lift. -/
def relativeSpectrumPointLocalAlgebraMap (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    A.obj ⟶ relativeSpectrumTarget (relativeSpectrumPointLocalBase A p) :=
  relativeSpectrumAtlasAlgebraMap A ≫
    relativeSpectrumTargetMap (relativeSpectrumDescentAtlasHomToX A) (relativeSpectrumPointAtlasLift A p) ≫
    eqToHom (congrArg relativeSpectrumTarget (relativeSpectrumPointAtlasLift_toX A p))

/-- A direct-image comma chart's actual scheme map to the point's test scheme. -/
def relativeSpectrumPointCommaToTest (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) : a.right.unop.left ⟶ T :=
  yoneda.preimage a.right.unop.hom

/-- A direct-image comma chart's actual scheme map to the base's étale chart. -/
def relativeSpectrumPointCommaToChart (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) : a.right.unop.left ⟶ W.left :=
  yoneda.preimage (a.hom.unop.left ≫ etaleBaseChangeSnd (relativeSpectrumPointBase A p) W)

/-- Pull the actual atlas cover back to a supplied direct-image comma chart. -/
def relativeSpectrumPointCommaCoverOver (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) : Over S :=
  pullback (relativeSpectrumPointCommaToTest A p W a) (relativeSpectrumPointAtlasToTest A p)

/-- The pulled-back covering scheme as a small étale chart of the test scheme. -/
def relativeSpectrumPointCommaCoverChart (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) : smallEtaleSite (ofOver T) :=
  @smallEtaleSite.mk S (ofOver T) (relativeSpectrumPointCommaCoverOver A p W a)
    (ofOverMap (pullback.fst (relativeSpectrumPointCommaToTest A p W a)
      (relativeSpectrumPointAtlasToTest A p) ≫ relativeSpectrumPointCommaToTest A p W a)) sorry

/-- The actual covering arrow to the original comma chart. -/
def relativeSpectrumPointCommaCoverToChart (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) : relativeSpectrumPointCommaCoverChart A p W a ⟶ a.right.unop :=
  MorphismProperty.CostructuredArrow.homMk
    (pullback.fst (relativeSpectrumPointCommaToTest A p W a) (relativeSpectrumPointAtlasToTest A p))
    trivial sorry

/-- The actual covering scheme also defines an étale chart of the point's atlas pullback. -/
def relativeSpectrumPointCommaLocalChart (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) : smallEtaleSite (ofOver (relativeSpectrumPointAtlasOver A p)) :=
  @smallEtaleSite.mk S (ofOver (relativeSpectrumPointAtlasOver A p))
    (relativeSpectrumPointCommaCoverOver A p W a)
    (ofOverMap (pullback.snd (relativeSpectrumPointCommaToTest A p W a)
      (relativeSpectrumPointAtlasToTest A p))) sorry

/-- The covering chart's actual arrow into the local-base fibre product with the base chart. -/
def relativeSpectrumPointCommaLocalEvaluationArrow (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) :
    (smallEtaleToSpaces (ofOver (relativeSpectrumPointAtlasOver A p))).obj
        (relativeSpectrumPointCommaLocalChart A p W a) ⟶
      (etaleBaseChange (relativeSpectrumPointLocalBase A p)).obj W :=
  MorphismProperty.Over.homMk
    ((pullback.lift (relativeSpectrumPointCommaLocalChart A p W a).hom
      (ofOverMap (pullback.fst (relativeSpectrumPointCommaToTest A p W a)
        (relativeSpectrumPointAtlasToTest A p) ≫ relativeSpectrumPointCommaToChart A p W a)) sorry :
      yoneda.obj (relativeSpectrumPointCommaCoverOver A p W a) ⟶
        (etaleBaseChangeSpace (relativeSpectrumPointLocalBase A p) W).functorOfPoints)) sorry

/-- The actual local algebra map evaluated on the native pulled-back cover. -/
def relativeSpectrumPointCommaLocalSectionMap (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) :
    QcAlgebraUnder.sectionRing A W ⟶
      (commStructureSheaf (ofOver T)).obj.obj (op (relativeSpectrumPointCommaCoverChart A p W a)) := by
  change QcAlgebraUnder.sectionRing A W ⟶
    Scheme.Γ.obj (op (relativeSpectrumPointCommaCoverOver A p W a).left)
  let evaluation :
      ((commRingPushforward (relativeSpectrumPointLocalBase A p)).obj
        (commStructureSheaf (ofOver (relativeSpectrumPointAtlasOver A p)))).obj.obj (op W) ⟶
      Scheme.Γ.obj (op (relativeSpectrumPointCommaCoverOver A p W a).left) :=
    commRingPushforwardEvaluation (relativeSpectrumPointLocalBase A p)
      (commStructureSheaf (ofOver (relativeSpectrumPointAtlasOver A p)))
      (relativeSpectrumPointCommaLocalEvaluationArrow A p W a)
  exact (InducedCategory.Hom.hom (relativeSpectrumPointLocalAlgebraMap A p).right).app (op W) ≫ evaluation

/-- The native pullback of the point's atlas cover covers each comma chart. -/
theorem relativeSpectrumPointCommaCover_mem (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) :
    Sieve.ofArrows (fun _ : Unit ↦ relativeSpectrumPointCommaCoverChart A p W a)
      (fun _ ↦ relativeSpectrumPointCommaCoverToChart A p W a) ∈
        (smallEtaleTopology (ofOver T)) a.right.unop := sorry

/-- The supplied descended atlas data give compatible actual section maps on each cover. -/
theorem relativeSpectrumPointCommaLocalSectionMap_compatible (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) {E : smallEtaleSite (ofOver T)}
    (b c : E ⟶ relativeSpectrumPointCommaCoverChart A p W a)
    (h : b ≫ relativeSpectrumPointCommaCoverToChart A p W a =
      c ≫ relativeSpectrumPointCommaCoverToChart A p W a) :
    relativeSpectrumPointCommaLocalSectionMap A p W a ≫ (commStructureSheaf (ofOver T)).obj.map b.op =
      relativeSpectrumPointCommaLocalSectionMap A p W a ≫ (commStructureSheaf (ofOver T)).obj.map c.op := sorry

/-- A comma-chart section map is actual native sheaf gluing of the supplied local map. -/
def relativeSpectrumPointCommaSectionMap (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op) :
    QcAlgebraUnder.sectionRing A W ⟶ (commStructureSheaf (ofOver T)).obj.obj (op a.right.unop) :=
  (commStructureSheaf (ofOver T)).property.amalgamateOfArrows
    (fun _ : Unit ↦ relativeSpectrumPointCommaCoverToChart A p W a)
    (relativeSpectrumPointCommaCover_mem A p W a)
    (fun _ ↦ relativeSpectrumPointCommaLocalSectionMap A p W a)
    (by
      intro E i j b c hab
      exact relativeSpectrumPointCommaLocalSectionMap_compatible A p W a b c hab)

/-- The actual reconstructed maps on all direct-image comma charts form the prescribed cone. -/
def relativeSpectrumPointAlgebraCone (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (W : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange (relativeSpectrumPointBase A p)).obj W))
      (smallEtaleToSpaces (ofOver T)).op ⋙ (commStructureSheaf (ofOver T)).obj) where
  pt := QcAlgebraUnder.sectionRing A W
  π := { app := fun a ↦ relativeSpectrumPointCommaSectionMap A p W a, naturality := sorry }

/-- Reconstruct the global algebra map of an original point by actual atlas gluing. -/
def relativeSpectrumPointAlgebraMap (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    A.obj ⟶ relativeSpectrumTarget (relativeSpectrumPointBase A p) :=
  Under.homMk
    ⟨{ app := fun W ↦ ConormalAlgebra.commRingPushforwardConeLift (relativeSpectrumPointBase A p)
          (commStructureSheaf (ofOver T)) W.unop (relativeSpectrumPointAlgebraCone A p W.unop)
       naturality := sorry }⟩ sorry

/-- Reconstructing a point's algebra map retains its supplied descended atlas encoding. -/
theorem relativeSpectrumPointAlgebraMap_restrict (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumAlgebraMap.ofHom (relativeSpectrumPointAlgebraMap A p) = p.2 := sorry

namespace relativeSpectrumAlgebraMap

/-- A descended atlas algebra map gives its original point with the specified actual base arrow. -/
def point {A : X.QcAlgebraUnder} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    relativeSpectrumPair A T :=
  ⟨yonedaEquiv g,
    cast (congrArg (relativeSpectrumAlgebraMap A) (Equiv.symm_apply_apply yonedaEquiv g).symm) e⟩

/-- The constructed point has exactly the prescribed base morphism. -/
theorem point_base {A : X.QcAlgebraUnder} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    relativeSpectrumPointBase A (point e) = g :=
  Equiv.symm_apply_apply yonedaEquiv g

/-- Effective reconstruction of a supplied descended map uses actual local section gluing. -/
def toHom {A : X.QcAlgebraUnder} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    A.obj ⟶ relativeSpectrumTarget g :=
  relativeSpectrumPointAlgebraMap A (point e) ≫ eqToHom (congrArg relativeSpectrumTarget (point_base e))

/-- Restricting the reconstructed global map recovers the original descended map. -/
theorem ofHom_toHom {A : X.QcAlgebraUnder} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    ofHom (toHom e) = e := sorry

/-- Reconstruction preserves every supplied global algebra map. -/
theorem toHom_ofHom {A : X.QcAlgebraUnder} {g : ofOver T ⟶ X} (α : A.obj ⟶ relativeSpectrumTarget g) :
    toHom (ofHom α) = α := sorry

/-- The global and descended encodings are equivalent by their actual restriction and gluing maps. -/
def homEquiv {A : X.QcAlgebraUnder} {g : ofOver T ⟶ X} :
    (A.obj ⟶ relativeSpectrumTarget g) ≃ relativeSpectrumAlgebraMap A g where
  toFun := ofHom
  invFun := toHom
  left_inv := toHom_ofHom
  right_inv := ofHom_toHom

end relativeSpectrumAlgebraMap

end AlgebraicGeometry.AlgebraicSpace
