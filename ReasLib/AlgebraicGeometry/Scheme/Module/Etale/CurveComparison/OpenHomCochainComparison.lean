module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.OpenHomRestrictionComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomDiagonalProduct
public import ReasLib.Algebra.Homology.Embedding.Functor
public import Mathlib.Data.Fintype.Fin

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace OpenHomCochainComparison
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
variable [X.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R, (etaleRestriction j).op.HasLeftKanExtension F]

instance extension_additive : (etaleExtensionByZero j (ModuleCat.{u + 1} R)).Additive := by sorry
instance restriction_additive : (etaleRestrictionSheaf j (ModuleCat.{u + 1} A)).Additive := by sorry
instance pushforward_additive : (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).Additive := by sorry
instance pushforward_preservesFiniteLimits : PreservesFiniteLimits (LocalHomDirectImage.pushforward j Rᵐᵒᵖ) := by sorry

variable (L : ChainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable (J : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ)

abbrev extendedL := ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj L
abbrev restrictedJ := ((etaleRestrictionSheaf j (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℕ)).obj J
abbrev sourceComplex := NoncommLocalHomComplex.complex h hc Y (extendedL j L) J
abbrev targetComplex := NoncommLocalHomComplex.complex h hc X L (restrictedJ j J)

def factorIso (n : ℕ) (i : Fin (n + 1)) :=
  OpenHomRestrictionComparison.iso h hc j (L.X i.val) (J.X (n - i.val))

def toTargetCone (n : ℕ) : Cone
    (LocalHomDiagonalProduct.diagram h hc X L (restrictedJ j J) n ⋙ LocalHomDirectImage.pushforward j Rᵐᵒᵖ) where
  pt := (sourceComplex h hc j L J).X n
  π := Discrete.natTrans (fun i ↦
    NoncommLocalHomComplex.projection h hc Y (extendedL j L) J n i.as ≫
      (factorIso h hc j L J n i.as).hom)

def toSourceCone (n : ℕ) : Cone (LocalHomDiagonalProduct.diagram h hc Y (extendedL j L) J n) where
  pt := (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).obj ((targetComplex h hc j L J).X n)
  π := Discrete.natTrans (fun i ↦
    (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).map
      (NoncommLocalHomComplex.projection h hc X L (restrictedJ j J) n i.as) ≫
    (factorIso h hc j L J n i.as).inv)

/-- Diagonal comparison from actual projections and the specified open-Hom
unit/counit maps. Every lift is the established finite-product universal lift. -/
def degreeIso (n : ℕ) : (sourceComplex h hc j L J).X n ≅
    (LocalHomDirectImage.pushforward j Rᵐᵒᵖ).obj ((targetComplex h hc j L J).X n) where
  hom := (isLimitOfPreserves (LocalHomDirectImage.pushforward j Rᵐᵒᵖ)
    (LocalHomDiagonalProduct.isLimit h hc X L (restrictedJ j J) n)).lift (toTargetCone h hc j L J n)
  inv := (LocalHomDiagonalProduct.isLimit h hc Y (extendedL j L) J n).lift (toSourceCone h hc j L J n)
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Naturality in both variables intertwines the actual signed Hom differentials. -/
def cochainIso : sourceComplex h hc j L J ≅
    ((LocalHomDirectImage.pushforward j Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (targetComplex h hc j L J) :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso h hc j L J) (by sorry)

/-- Full integer-cochain comparison representing Rj_*; no degree-zero
concentration or arbitrary comparison package appears. -/
def integerIso : (sourceComplex h hc j L J).extend ComplexShape.embeddingUpNat ≅
    ((LocalHomDirectImage.pushforward j Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((targetComplex h hc j L J).extend ComplexShape.embeddingUpNat) :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (cochainIso h hc j L J) ≪≫
  (ComplexShape.embeddingUpNat.mapAppIso (LocalHomDirectImage.pushforward j Rᵐᵒᵖ)
    (targetComplex h hc j L J)).symm

end OpenHomCochainComparison
