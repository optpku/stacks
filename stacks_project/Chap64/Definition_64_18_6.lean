module

public import stacks_project.Chap64.Definition_64_18_6_QEll
public import stacks_project.Chap64.Definition_64_18_6_Stalk
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Etale

/- Definition 64.18.6 (1): a ℤ_[ℓ]-sheaf F is torsion if ℓ ^ n : F ⟶ F is the
zero map for some n. -/
@[stacks 03UR] #check ZEllSheaf.IsTorsion

/- Definition 64.18.6 (2): the abelian category of ℚ_[ℓ]-sheaves on a Noetherian
scheme X is the quotient of the abelian category of ℤ_[ℓ]-sheaves by the Serre
subcategory of torsion sheaves; objects remain ℤ_[ℓ]-sheaves, and
Hom_{ℚ_[ℓ]}(F, G) = Hom_{ℤ_[ℓ]}(F, G) ⊗[ℤ_[ℓ]] ℚ_[ℓ], as qellHom. -/
@[stacks 03UR] #check ZEllSheaf.qellHom

/- Definition 64.18.6 (3): the quotient functor is F ↦ F ⊗ ℚ_[ℓ], acting as the
identity on objects and by tensorQEll on morphisms. -/
@[stacks 03UR] #check ZEllSheaf.tensorQEll

/- Definition 64.18.6 (4): if F = F' ⊗ ℚ_[ℓ] for a ℤ_[ℓ]-sheaf F' and x̄ is a
geometric point, the stalk of F at x̄ is F'_x̄ ⊗ ℚ_[ℓ], as qellStalk. -/
@[stacks 03UR] #check ZEllSheaf.qellStalk
