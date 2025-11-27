import Mathlib

structure IsoData {n: ℕ} {G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)} (g: G) where
  a : ℕ
  ha: a ≠ 0
  A: Subgroup (Matrix.unitaryGroup (Fin a) ℂ)
  B: Subgroup (Matrix.unitaryGroup (Fin (n - a)) ℂ)
  iso: Subgroup.centralizer {g} ≃* A × B

lemma diag_of_eigenspace_span {n: ℕ} [hn: NeZero n] (g: ((Fin n) → ℂ) →ₗ[ℂ] (Fin n) → ℂ) (k: ℂ) (hg: Module.End.eigenspace g k = ⊤):
  g = k • 1 := by

  rw [LinearMap.ext_iff]
  intro x
  simp

  have has_eigenvalue: Module.End.HasEigenvalue g k := by
    rw [Module.End.hasEigenvalue_iff, hg]
    simp

  have x_mem: x ∈ Module.End.eigenspace g k := by
    simp [hg]

  rw [Module.End.mem_eigenspace_iff] at x_mem
  exact x_mem

lemma linearmap_comp_eq_mul {P: Type*} [AddCommMonoid P] [Module ℂ P] (a b: P →ₗ[ℂ] P): a.comp b = a * b := rfl

set_option maxHeartbeats 300000 in
set_option synthInstance.maxHeartbeats 40000 in
lemma centralizer_iso {n: ℕ} [hn: NeZero n] (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g: G) (g_not: ∀ z: ℂ, g.val.val ≠ z • 1):
    Nonempty (IsoData g) := by



  obtain ⟨k, hk⟩ := Module.End.exists_eigenvalue g.val.val.toLin'
  by_cases gen_eigenspace_top: Module.End.maxGenEigenspace g.val.val.toLin' k = ⊤
  .

    have eigenspace_top: Module.End.eigenspace g.val.val.toLin' k = ⊤ := by
      ext a
      simp
      have a_mem_top: a ∈ (⊤ : (Submodule ℂ (Fin n → ℂ))) := by simp
      rw [← gen_eigenspace_top] at a_mem_top
      simp at a_mem_top
      sorry

    rw [Module.End.maxGenEigenspace_eq] at gen_eigenspace_top
    apply Module.End.HasEigenvalue.exists_hasEigenvector at hk

    have eq_diag := diag_of_eigenspace_span g.val.val.toLin' k eigenspace_top
    specialize g_not k
    apply_fun (fun f => f.toMatrix') at eq_diag
    simp at eq_diag
    contradiction
  .
    have span := Module.End.iSup_maxGenEigenspace_eq_top g.val.val.toLin'
    rw [iSup_split_single _ k] at span
    rw [← codisjoint_iff] at span

    have other_ne_bot := Codisjoint.ne_bot_of_ne_top span gen_eigenspace_top
    rw [codisjoint_iff] at span

    have preserves := Module.End.mapsTo_genEigenspace_of_comm (f := g.val.val.toLin') (g := g.val.val.toLin') (by simp) k (Module.End.maxGenEigenspaceIndex g.val.val.toLin' k)
    rw [← Module.End.maxGenEigenspace_eq] at preserves
    rw [← iSup_ne_bot_subtype] at span

    have new_ne_bot: ⨆ (i : Module.End.Eigenvalues g.val.val.toLin'), ⨆ (_: i.val ≠ k), Module.End.maxGenEigenspace g.val.val.toLin' i ≠ ⊥ := by
      sorry



    -- nth_rw 1 [iSup_subtype] at span
    -- simp at span
    -- conv at span =>
    --   lhs
    --   rhs
    --   arg 1
    --   intro i
    --   arg 1
    --   intro hi


    have other_invariant:  ⨆ (i : { i : Module.End.Eigenvalues g.val.val.toLin' // i.val ≠ k }), Module.End.maxGenEigenspace g.val.val.toLin' i ∈ (Module.End.invtSubmodule g.val.val.toLin') := by
      apply SupClosed.iSup_mem
      . simp
      . simp
      .
        intro i
        simp
        apply Module.End.mapsTo_genEigenspace_of_comm
        simp

    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at other_invariant


    let map_first (h: Subgroup.centralizer {g}) := h.val.val.val.toEuclideanLin.restrict (Module.End.mapsTo_genEigenspace_of_comm (f := g.val.val.toEuclideanLin) (g := h.val.val.val.toEuclideanLin) (by
      have foo := h.property
      rw [Subgroup.mem_centralizer_iff] at foo
      rw [commute_iff_eq]
      simp at foo
      apply_fun (fun m => m.val.val.toEuclideanLin) at foo
      simp only [Subgroup.coe_mul, Submonoid.coe_mul] at foo
      unfold Matrix.toEuclideanLin at foo
      simp only [LinearEquiv.trans_apply, Matrix.toLin'_mul] at foo
      unfold Matrix.toEuclideanLin
      exact foo
    ) k ⊤)

    --let d := Module.finrank ℂ (Module.End.genEigenspace g.val.val.toEuclideanLin k ⊤)
    let d := (Module.finrank ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ ↥((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤)))))
    let map_first_unitary (h: Subgroup.centralizer {g}): Matrix.unitaryGroup (Fin d) ℂ := {
      val := (LinearMap.toMatrix (Module.finBasisOfFinrankEq _ _ rfl) (Module.finBasisOfFinrankEq _ _ rfl) (map_first h)).toEuclideanLin.toMatrixOrthonormal (stdOrthonormalBasis _ _)
      property := by


        rw [Matrix.mem_unitaryGroup_iff]

        conv =>
          lhs
          rhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [Matrix.star_eq_conjTranspose]
        -- rw [← LinearMap.toMatrix_adjoint]
        -- simp

        simp only [LinearMap.toMatrixOrthonormal_apply]
        simp []
        conv =>
          lhs
          rhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [← LinearMap.toMatrix_adjoint]
        rw [← LinearMap.toMatrix_mul]
        conv =>
          lhs
          rhs
          rhs
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
          arg 1
          rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]


        conv =>
          lhs
          rhs
          arg 1
          arg 1
          rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]


        apply_fun Matrix.toLin (stdOrthonormalBasis _ _).toBasis (stdOrthonormalBasis _ _).toBasis
        simp
        conv =>
          lhs
          rw [← linearmap_comp_eq_mul]
          rw [← Matrix.toLin_mul]
          -- rhs

          -- rw [← Matrix.toLin_mul]
          -- rw [← LinearMap.toMatrix_mul]

        apply_fun LinearMap.toMatrix (stdOrthonormalBasis _ _).toBasis (stdOrthonormalBasis _ _).toBasis
        simp [LinearMap.toMatrix_id]
        sorry
    }

    let map_first_hom: MonoidHom (Subgroup.centralizer {g}) _ := {
      toFun := map_first_unitary
      map_one' := by
        simp [map_first_unitary, map_first]
        sorry
        -- rw [LinearMap.ext_iff]
        -- intro x
        -- rw [LinearMap.restrict_apply]
        -- simp
      map_mul' := by
        intro x y
        sorry
        -- simp [map_first]
        -- rfl
    }

    let first_range := map_first_hom.range


    let map_second (h: Subgroup.centralizer {g}) := h.val.val.val.toLin'.restrict
      (p :=  ⨆ (i : { i : Module.End.Eigenvalues g.val.val.toLin' // i.val ≠ k }), Module.End.maxGenEigenspace g.val.val.toLin' i)
      (q :=  ⨆ (i : { i : Module.End.Eigenvalues g.val.val.toLin' // i.val ≠ k }), Module.End.maxGenEigenspace g.val.val.toLin' i)
      (by
        intro x hx
        sorry
      )

    let map_second_unitary (h: Subgroup.centralizer {g}): Matrix.unitaryGroup (Fin (n - d)) ℂ := {
      val := by
        let foo := (map_second h)
        sorry
      property := sorry
    }

    let map_second_hom: MonoidHom (Subgroup.centralizer {g}) _ := {
      toFun := map_second_unitary
      map_one' := by
        simp [map_second_unitary, map_second]
        sorry
        -- rw [LinearMap.ext_iff]
        -- intro x
        -- rw [LinearMap.restrict_apply]
        -- simp
      map_mul' := by
        intro x y
        sorry
        -- simp [map_first]
        -- rfl
    }

    let first_iso := MonoidHom.ofInjective (f := map_first_hom) (by sorry)
    let second_iso := MonoidHom.ofInjective (f := map_second_hom) (by sorry)
    let prod_hom := MonoidHom.prod first_iso.toMonoidHom second_iso.toMonoidHom
    let prod_iso := MulEquiv.ofBijective prod_hom (by
      unfold Function.Bijective
      refine ⟨?_, ?_⟩
      .
        simp [prod_hom]
        intro x y hxy
        simpa using hxy
      .
        intro a
        sorry
    )


    apply Nonempty.intro
    exact {
      a := Module.finrank ℂ (Module.End.genEigenspace g.val.val.toLin' k (Module.End.maxGenEigenspaceIndex g.val.val.toLin' k))
      ha := by
        rw [Nat.ne_zero_iff_zero_lt]
        apply Module.End.pos_finrank_genEigenspace_of_hasEigenvalue hk
        simp [Module.End.maxGenEigenspaceIndex]
        sorry
      A := _
      B := _
      iso := prod_iso

    }


  -- let f: Subgroup.centralizer {g} ≃* A × B := {

  -- }
  -- sorry
