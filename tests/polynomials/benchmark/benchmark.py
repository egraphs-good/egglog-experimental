#!/usr/bin/env python3
import random
import subprocess
import time
import os
import matplotlib.pyplot as plt
from typing import Tuple
import sympy as sp
from sympy import symbols, expand

def generate_factored_polynomial(target_terms: int) -> Tuple[sp.Expr, sp.Expr, int]:
    """Generate a factored polynomial and its expanded form using SymPy."""
    v, w, x, y, z = symbols('v, w x y z')
    variables = [v, w, x, y, z]
    
    # Generate factors to reach approximately target_terms
    if target_terms <= 4:
        # Simple binomial
        var1, var2 = random.sample(variables, 2)
        coeff = random.randint(1, 3)
        factored = (var1 + coeff * var2) ** 2
    elif target_terms <= 8:
        # Binomial with higher power
        var1, var2 = random.sample(variables, 2)
        coeff = random.randint(1, 2)
        power = min(3, max(2, target_terms // 3))
        factored = (var1 + coeff * var2) ** power
    elif target_terms <= 15:
        # Product of two binomials
        var1, var2, var3 = random.sample(variables, 3)
        coeff1, coeff2 = random.randint(1, 2), random.randint(1, 2)
        factored = (var1 + coeff1 * var2) * (var2 + coeff2 * var3)
    else:
        # More complex factored form
        var1, var2, var3, var4, var5 = variables
        coeff1, coeff2, coeff3, coeff4 = random.randint(1, 2), random.randint(1, 2), random.randint(1, 3), random.randint(1, 3)
        power = min(3, max(2, target_terms // 6))
        factored = (var1 + coeff1 * var2) ** power * (var2 + coeff3 * var3) * (var4 + coeff4 * var5) ** 2
    
    # Expand the polynomial
    expanded = expand(factored)
    
    # Count actual terms in expanded form
    if expanded.is_Add:
        actual_terms = len(expanded.args)
    else:
        actual_terms = 1
    
    return factored, expanded, actual_terms

def sympy_to_egglog(expr: sp.Expr) -> str:
    """Convert SymPy expression to egglog polynomial format."""
    
    def convert_expr(e):
        if e.is_Symbol:
            return f'(Var "{e}")'
        elif e.is_Number:
            if e == 0:
                return "(Zero)"
            elif e == 1:
                return "(One)"
            else:
                return f"(Coefficient {int(e)}.0 (One))"
        elif e.is_Add:
            args = [convert_expr(arg) for arg in e.args]
            result = args[0]
            for arg in args[1:]:
                result = f"(Add {result} {arg})"
            return result
        elif e.is_Mul:
            # Separate coefficient from the rest
            coeff = 1
            factors = []
            for arg in e.args:
                if arg.is_Number:
                    coeff *= arg
                else:
                    factors.append(arg)
            
            if not factors:
                return convert_expr(coeff)
            
            # Convert factors
            factor_strs = [convert_expr(f) for f in factors]
            result = factor_strs[0]
            for f in factor_strs[1:]:
                result = f"(Mul {result} {f})"
            
            # Apply coefficient if not 1
            if coeff != 1:
                if coeff == -1:
                    result = f"(Coefficient -1.0 {result})"
                else:
                    result = f"(Coefficient {int(coeff)}.0 {result})"
            
            return result
        elif e.is_Pow:
            base = convert_expr(e.base)
            exp = int(e.exp)
            return f"(Power {base} {exp})"
        else:
            # Fallback for other expressions
            return f'(Var "unknown")'
    
    return convert_expr(expr)

def create_egglog_test(factored_egglog: str, expanded_egglog: str, test_type: str) -> str:
    """Create egglog test string for basic or SMT."""
    
    if test_type == "basic":
        include_line = '(include "polynomial-basic-rules.egg")'
        use_smt = ""
    else:  # smt
        include_line = '(include "polynomial-smt-rules.egg")'
        use_smt = """
(let _e1 (UseSmt e1))
(let _e2 (UseSmt e2))"""
    
    return f"""; Generated polynomial benchmark test
{include_line}

; Factored polynomial
(let e1 {factored_egglog})

; Expanded polynomial
(let e2 {expanded_egglog})
{use_smt}

(run-schedule (saturate (run)))
(check (= e1 e2))
"""

def run_benchmark(test_file: str, timeout: int = 120) -> Tuple[float, str]:
    """Run egglog test and return (execution time, status)."""
    binary_path = "../../../target/debug/egglog-experimental"
    
    start_time = time.time()
    try:
        result = subprocess.run([binary_path, test_file], 
                              capture_output=True, text=True, timeout=timeout)
        end_time = time.time()
        
        if result.returncode != 0:
            print(f"Error running {test_file}: {result.stderr}")
            return end_time - start_time, "error"
            
        return end_time - start_time, "success"
    except subprocess.TimeoutExpired:
        print(f"Timeout ({timeout}s) exceeded for {test_file}")
        return timeout, "timeout"

def main():
    # Test parameters
    term_counts = [3, 5, 8, 12, 16, 20, 25, 30]
    results = {"basic_times": [], "smt_times": [], "basic_status": [], "smt_status": [], "terms": []}
    
    os.makedirs("temp_tests", exist_ok=True)
    
    for target_terms in term_counts:
        print(f"Testing {target_terms} terms...")
        
        # Generate polynomial using SymPy
        factored_sympy, expanded_sympy, actual_terms = generate_factored_polynomial(target_terms)
        
        # Convert to egglog format
        factored_egglog = sympy_to_egglog(factored_sympy)
        expanded_egglog = sympy_to_egglog(expanded_sympy)
        
        print(f"  SymPy factored: {factored_sympy}")
        print(f"  SymPy expanded: {expanded_sympy}")
        print(f"  Actual terms: {actual_terms}")
        
        # Test basic rewrite rules
        basic_test = create_egglog_test(factored_egglog, expanded_egglog, "basic")
        basic_file = f"temp_tests/test_basic_{target_terms}.egg"
        
        with open(basic_file, 'w') as f:
            f.write(basic_test)
        
        basic_time, basic_status = run_benchmark(basic_file, timeout=30)
        
        # Test SMT rules  
        smt_test = create_egglog_test(factored_egglog, expanded_egglog, "smt")
        smt_file = f"temp_tests/test_smt_{target_terms}.egg"
        
        with open(smt_file, 'w') as f:
            f.write(smt_test)
            
        smt_time, smt_status = run_benchmark(smt_file, timeout=30)
        
        # Store all results
        results["terms"].append(actual_terms)
        results["basic_times"].append(basic_time)
        results["smt_times"].append(smt_time)
        results["basic_status"].append(basic_status)
        results["smt_status"].append(smt_status)
        
        print(f"  Basic: {basic_time:.3f}s ({basic_status}), SMT: {smt_time:.3f}s ({smt_status})")
    
    # Generate graph with connected lines and different markers
    plt.figure(figsize=(12, 8))
    
    # Plot basic line with different markers
    basic_markers = ['o' if s == 'success' else 'x' if s == 'timeout' else '^' for s in results["basic_status"]]
    plt.plot(results["terms"], results["basic_times"], 'b-', label='Basic Rewrites', alpha=0.7)
    for i, (x, y, marker) in enumerate(zip(results["terms"], results["basic_times"], basic_markers)):
        plt.scatter(x, y, marker=marker, s=80, c='blue', zorder=5)
    
    # Plot SMT line with different markers  
    smt_markers = ['o' if s == 'success' else 'x' if s == 'timeout' else '^' for s in results["smt_status"]]
    plt.plot(results["terms"], results["smt_times"], 'r-', label='SMT Rewrites', alpha=0.7)
    for i, (x, y, marker) in enumerate(zip(results["terms"], results["smt_times"], smt_markers)):
        plt.scatter(x, y, marker=marker, s=80, c='red', zorder=5)
    
    # Add legend for markers
    plt.scatter([], [], marker='o', s=80, c='gray', label='Success')
    plt.scatter([], [], marker='x', s=80, c='gray', label='Timeout') 
    plt.scatter([], [], marker='^', s=80, c='gray', label='Error')
    
    plt.xlabel('Number of Terms in Expanded Polynomial')
    plt.ylabel('Runtime (seconds)')
    plt.title('Egglog Performance: Basic vs SMT Rewrites')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.savefig('graphs/polynomial_benchmark.png', dpi=300, bbox_inches='tight')
    plt.show()
    
    # Save results
    with open('results/benchmark_results.txt', 'w') as f:
        f.write("Terms,Basic_Time,Basic_Status,SMT_Time,SMT_Status\n")
        for i in range(len(results["terms"])):
            f.write(f"{results['terms'][i]},{results['basic_times'][i]:.3f},{results['basic_status'][i]},{results['smt_times'][i]:.3f},{results['smt_status'][i]}\n")

if __name__ == "__main__":
    main()
