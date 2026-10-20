module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.ClosedCover
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 33.38.8

Invertible modules and suitable sections glue across finite closed covers of a
reduced scheme whose pairwise intersections are discrete.
-/

universe u

/- Lemma 33.38.8: invertible modules on a finite closed cover of a reduced scheme with
discrete pairwise intersections glue to an invertible module on the ambient scheme. -/
@[stacks 09NE] #check
  (AlgebraicGeometry.Scheme.Modules.ClosedCover.existsInvertibleModule :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsReduced X]
      {n : ℕ} (Z : Fin n → X.IdealSheafData)
      (L : (i : Fin n) → (Z i).subscheme.Modules)
      [∀ i : Fin n, AlgebraicGeometry.Scheme.Modules.Invertible (L i)]
      (h_cover : (⋃ i, ((Z i).support : Set X)) = Set.univ)
      (h_discrete : ∀ i j : Fin n, i ≠ j →
        IsDiscrete (((Z i).support : Set X) ∩ ((Z j).support : Set X))),
      ∃ (M : X.Modules) (_ : AlgebraicGeometry.Scheme.Modules.Invertible M),
        Nonempty (∀ i : Fin n,
          (AlgebraicGeometry.Scheme.Modules.pullback (Z i).subschemeι).obj M ≅ L i))

/- Lemma 33.38.8 (sections): sections nonvanishing on the pairwise intersections glue to a
global section of the glued invertible module. -/
@[stacks 09NE] #check
  (AlgebraicGeometry.Scheme.Modules.ClosedCover.existsInvertibleModuleWithSection :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsReduced X]
      {n : ℕ} (Z : Fin n → X.IdealSheafData)
      (L : (i : Fin n) → (Z i).subscheme.Modules)
      [∀ i : Fin n, AlgebraicGeometry.Scheme.Modules.Invertible (L i)]
      (s : ∀ i : Fin n, (L i).sections)
      (h_cover : (⋃ i, ((Z i).support : Set X)) = Set.univ)
      (h_discrete : ∀ i j : Fin n, i ≠ j →
        IsDiscrete (((Z i).support : Set X) ∩ ((Z j).support : Set X)))
      (h_nonvanishing : ∀ i j : Fin n, i ≠ j →
        ((Z i).support : Set X) ∩ ((Z j).support : Set X) ⊆
          AlgebraicGeometry.Scheme.Modules.ClosedCover.sectionNonvanishingImage
            (Z i) (L i) (s i)),
      ∃ (M : X.Modules) (_ : AlgebraicGeometry.Scheme.Modules.Invertible M)
        (t : M.sections)
        (e : ∀ i : Fin n,
          (AlgebraicGeometry.Scheme.Modules.pullback (Z i).subschemeι).obj M ≅ L i),
        ∀ i : Fin n,
          AlgebraicGeometry.Scheme.Modules.ClosedCover.sectionCompatible
            (Z i) t (s i) (e i))
