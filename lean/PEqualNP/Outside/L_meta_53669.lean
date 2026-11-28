import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_53669 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (3995131 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  let C : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [10, 15]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [5, 17]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [18, 19]⟩], 20⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
