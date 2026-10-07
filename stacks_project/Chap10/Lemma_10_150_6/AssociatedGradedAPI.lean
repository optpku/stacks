module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

@[expose] public section

-- Minimal associated-graded API isolated for Lemma 10.150.6.
--
-- The shared associated-graded declarations (`Ideal.AssociatedGraded.ring`,
-- `Ideal.AssociatedGraded.map`, `Ideal.AssociatedGraded.grade`, the graded-module
-- pieces, ...) are owned by `ReasLib.RingTheory.Ideal.AssociatedGraded.Basic`.
-- This file only keeps the helper unique to Lemma 10.150.6.

#check @ReesAlgebra.Grading.map_mem_grade
