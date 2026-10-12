/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Adic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CompactSupport
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

section Global

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]

/- Definition 64.18.8 (1): if X is a separated scheme of finite type over an
algebraically closed field k and F is a ℤ_[ℓ]-sheaf on X, the ℓ-adic cohomology
is H^i(X, F) := lim_n H^i(X, F_n). -/
@[stacks 03UT] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.cohomology :
  ZEllSheaf X.left ℓ → ℕ → AddCommGrpCat.{u})

end Global

section CompactSupport

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- Definition 64.18.8 (2): in the same setting, compactly supported ℓ-adic
cohomology is H_c^i(X, F) := lim_n H_c^i(X, F_n), computed as the inverse limit
of the cohomology of the extension by zero of each stage along a
compactification. -/
@[stacks 03UT] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.cohomologyCompactSupport :
  ∀ (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})],
    ZEllSheaf X.left ℓ → ℕ → AddCommGrpCat.{u})

/- Definition 64.18.8 (3): if F = F' ⊗ ℚ_[ℓ] for a ℤ_[ℓ]-sheaf F', then
H_c^i(X, F) := H_c^i(X, F') ⊗[ℤ_[ℓ]] ℚ_[ℓ], as extension of scalars of the
ℤ_[ℓ]-module H_c^i(X, F'). -/
@[stacks 03UT] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.cohomologyCompactSupportQEll :
  ∀ (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})],
    ZEllSheaf X.left ℓ → ℕ → ModuleCat.{u} ℚ_[ℓ])

/- Compactification is a presentation choice: any two choices give isomorphic
compactly supported ℓ-adic cohomology groups. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.cohomologyCompactSupport_independent :
  ∀ (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]
    (Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι Q)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι Q)).op.HasLeftKanExtension G]
    [HasWeakSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]
    (F : ZEllSheaf X.left ℓ) (i : ℕ),
    Nonempty (ZEllSheaf.cohomologyCompactSupport P F i ≅
      ZEllSheaf.cohomologyCompactSupport Q F i))

end CompactSupport
