# -*- coding: utf-8 -*-
"""H2 dependency DAG (single merged graph, English).
Edges are derived mechanically from source blocks by build_dag.py (never hand-written).
Node = (id, label, file_tag, layer, kind, decl_name)."""

NODES = [
    ("root",   "H2:  Z_{S9}(F,9) ≅ F(M⊕U)^{S9}", "Statement.lean:127", 0, "root", None),

    # --- main chain ---
    ("h2unc",  "h2_unconditional",                        "UDKScalarMem", 1, "self", "h2_unconditional"),
    ("nv9",    "nonempty_genericDivisionData_two_nine",   "Nonvacuous", 1, "self", "nonempty_genericDivisionData_two_nine"),
    ("h2sm",   "h2_of_scalarMem",                         "UDKSimple", 2, "self", "h2_of_scalarMem"),
    ("smz",    "scalarMemZHypK'",                         "UDKScalarMem", 2, "self", "scalarMemZHypK'"),
    ("nv2",    "nonempty_genericDivisionData_two",        "Nonvacuous", 2, "self", "nonempty_genericDivisionData_two"),
    ("simp",   "isSimpleRing_UDK'_of_scalarMem",          "UDKSimple", 3, "self", "isSimpleRing_UDK'_of_scalarMem"),
    ("nvspan", "nonempty_genericDivisionData_of_span",    "Cor148", 3, "self", "nonempty_genericDivisionData_of_span"),
    ("hspan",  "adjoin_genericMatrix_map_eq_top",         "Nonvacuous", 3, "self", "adjoin_genericMatrix_map_eq_top"),
    ("ideal",  "udk'_ideal_inf_scalars",                  "UDKSimple", 4, "self", "udk'_ideal_inf_scalars"),
    ("nvac",   "exists_scalar_mem_of_ne_bot",             "PI/CentralIdeal", 5, "self", "exists_scalar_mem_of_ne_bot"),
    ("cor148", "exists_scalar_map_of_mem_genericCenter_of_span",                             "Cor148", 4, "self", "exists_scalar_map_of_mem_genericCenter_of_span"),
    ("clear",  "exists_clear_den",                        "ScalarMemZ", 3, "self", "exists_clear_den"),
    ("centimg","mem_centerImage_of_map_eq_scalar",        "ScalarMemZ", 3, "self", "mem_centerImage_of_map_eq_scalar"),
    ("scalarm","scalar_mem_sprAlgebraK_of_mem_subring",   "UDKScalarMem", 3, "self", "scalar_mem_sprAlgebraK_of_mem_subring"),
    ("detmap", "det_phiS_map_ne_zero",                    "Nonvacuous", 4, "self", "det_phiS_map_ne_zero"),

    # --- lower layers ---
    ("spralg", "mem_sprAlgebraK_iff",                     "UDKSpan", 4, "self", "mem_sprAlgebraK_iff"),
    ("centk",  "psiSpr_center_scalar",                    "H2Final", 4, "self", "psiSpr_center_scalar"),
    ("centiff","mem_genericCenter_iff",                   "GenericMatrix", 4, "self", "mem_genericCenter_iff"),
    ("mcenter2","exists_eq_scalar_of_mem_matrixCenter",    "GenericMatrix", 5, "self", "exists_eq_scalar_of_mem_matrixCenter"),
    ("mcenter","matrixCenter_eq_bot",                      "GenericMatrix", 6, "self", "matrixCenter_eq_bot"),

    # --- numeric layer ---
    ("dets",   "det_phiS_ne_zero",                        "GenericSpan", 5, "self", "det_phiS_ne_zero"),
    ("detpsi", "det_psi_ne_zero",                         "GenericSpan", 6, "self", "det_psi_ne_zero"),
    ("phimap", "phiS_map_evalAt",                         "GenericSpan", 6, "self", "phiS_map_evalAt"),
    ("lam",    "lam_injective",                           "GenericSpan", 7, "self", "lam_injective"),

    # --- mathlib (only those used directly) ---
    ("m_induct","Algebra.adjoin_induction",                "mathlib", 5, "mathlib", None),
    ("m_inv",  "Matrix.nonsing_inv_mul",                  "mathlib", 4, "mathlib", None),
    ("m_mapdet","RingHom.map_det",                        "mathlib", 6, "mathlib", None),
    ("m_cent", "Subalgebra.mem_center_iff",                "mathlib", 7, "mathlib", None),
    ("m_det",  "Matrix.det_kronecker ＋ det_vandermonde",   "mathlib", 7, "mathlib", None),
    ("m_pow",  "Matrix.map_pow ＋ diagonal_pow/mul_diagonal", "mathlib", 7, "mathlib", None),
]

MERGE = {"m_kron": "m_det", "m_vand": "m_det", "m_diag": "m_pow", "m_scalar": None}

EXTRA_EXT = {
    "m_induct": "adjoin_induction", "m_inv": "nonsing_inv_mul", "m_mapdet": "map_det",
    "m_cent": "mem_center_iff", "m_det": "det_kronecker",
    "m_vand": "det_vandermonde_ne_zero_iff", "m_pow": "map_pow", "m_diag": "diagonal_pow",
    "m_scalar": "mem_range_scalar_iff_commute_single",
}

TITLE = "Dependency graph of the formalized Procesi identification (H2) in Lean 4"

LEGEND = [
    ("box_self", "self-authored theorem (the Lean file is given)"),
    ("box_math", "mathlib lemma, used directly"),
    ("arrow",    "uses"),
]

NOTES = [
    "Edges are derived mechanically from the Lean sources (declaration blocks, comments stripped); "
    "none are hand-written.",
    "Axiom profile of every theorem shown: propext, Classical.choice, Quot.sound (sorryAx = 0).",
]
