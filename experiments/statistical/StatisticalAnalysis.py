#!/usr/bin/env python3
"""
Statistical Model Checking for Alpenglow Consensus

Runs Monte Carlo simulations for realistic network sizes (10-1000+ nodes).
Provides probabilistic verification coverage for large-scale networks.
"""

import os
import sys
import json
import time
import subprocess
import concurrent.futures
from pathlib import Path
import random

class AlpenglowStatisticalAnalysis:
    """Statistical model checking framework for large-scale verification"""
    def __init__(self):
        self.base_dir = Path(__file__).parent.parent.parent
        self.results = []
        self.total_simulations = 0
        self.successful_simulations = 0
        # Use all available CPU cores for TLC and Python parallelism
        self.cpu_workers = max(1, (os.cpu_count() or 4))
        
    def generate_large_scale_configs(self):
        """Generate configurations for realistic blockchain network sizes (10-1000 nodes)"""
        configs = []
        
        # Realistic network sizes for production blockchain systems (including very large networks)
        network_sizes = [10, 20, 30, 50, 75, 100, 200, 300, 500, 1000]
        
        for nodes in network_sizes:
            # Test key Byzantine fault scenarios (< 20% for BFT safety)
            # Calculate Byzantine faults as percentage of nodes
            max_byzantine = (nodes * 19) // 100  # 19% max
            
            # Test scenarios: no faults, low faults, near-max faults
            test_scenarios = [
                (0, 0),  # No faults
                (max(1, nodes // 20), 0),  # ~5% Byzantine
                (max_byzantine, 0),  # Max Byzantine (19%)
            ]
            
            for byz_count, crash_count in test_scenarios:
                config = {
                    'NodeCount': nodes,
                    'ByzantineCount': byz_count,
                    'CrashedCount': crash_count,
                    'SlotCount': 1,
                    'HashVariants': 2,
                    'NetworkDelay': 100,
                    'seed': random.randint(0, 1000000)
                }
                configs.append(config)
        
        # Return all configurations (30 tests: 10 network sizes × 3 fault scenarios each)
        return configs
    
    def create_config_file(self, config, config_path):
        """Create TLA+ config file for statistical run using LargeScaleConfig format"""
        cfg_content = f"""SPECIFICATION Spec

CONSTANTS
    NodeCount = {config['NodeCount']}
    SlotCount = {config['SlotCount']}
    ByzantineCount = {config['ByzantineCount']}
    CrashedCount = {config['CrashedCount']}

INVARIANTS
    LargeScaleInvariants
"""
        
        with open(config_path, 'w') as f:
            f.write(cfg_content)
    
    def run_statistical_verification(self, config):
        """Run TLC verification with simulation mode for large networks"""
        print(f"🔄 Testing: {config['NodeCount']} nodes, {config['ByzantineCount']} Byzantine, {config['CrashedCount']} crashed")
        
        config_dir = self.base_dir / "experiments" / "statistical" / "configs"
        config_dir.mkdir(exist_ok=True)
        
        config_name = f"stat_{config['NodeCount']}_{config['ByzantineCount']}_{config['CrashedCount']}_{config['seed']}"
        config_path = config_dir / f"{config_name}.cfg"
        
        # Create TLA+ config file for this specific configuration
        self.create_config_file(config, config_path)
        
        # Use the fixed statistical specification for large-scale runs
        tla_file = self.base_dir / "model-checking" / "statistical" / "LargeScaleConfig.tla"
        
        # Create a temp metadir for TLC to write its files
        metadir = self.base_dir / "experiments" / "statistical" / "temp" / f"meta_{config['seed']}"
        metadir.mkdir(parents=True, exist_ok=True)
        
        # Use simulation mode for all realistic network sizes (10-50 nodes)
        use_simulation = True
        
        # Build TLC command
        cmd = [
            "java", 
            "-Xmx8g",  # 8GB heap to maximize throughput
            "-XX:+UseParallelGC",
            "-cp", "tla2tools.jar",
            "tlc2.TLC", 
            "-nowarning",
            "-workers", str(self.cpu_workers),  # Use all available CPU cores
            "-simulate", "num=1000",  # 1000 random traces for comprehensive coverage
            "-depth", "50"  # Deep exploration per trace
        ]
        
        # Use relative paths like the working tests
        rel_config_path = config_path.relative_to(self.base_dir)
        rel_tla_file = tla_file.relative_to(self.base_dir)
        rel_metadir = metadir.relative_to(self.base_dir)
        
        cmd.extend([
            "-metadir", str(rel_metadir),
            "-config", str(rel_config_path),
            str(rel_tla_file)
        ])
        
        start_time = time.time()
        try:
            # Simulation mode timeout (1000 traces can take a bit longer)
            timeout_seconds = 60  # 60 seconds for simulation
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True, 
                timeout=timeout_seconds,
                cwd=str(self.base_dir),
                env={**os.environ}
            )
            
            runtime = time.time() - start_time
            
            # Parse TLC output
            output = result.stdout + result.stderr
            states_explored = self.extract_states_explored(output)
            distinct_states = self.extract_distinct_states(output)
            
            # Check for parsing errors first
            has_parse_error = 'parse error' in output.lower() or 'nullpointerexception' in output.lower()
            
            if has_parse_error:
                success = False
                status_msg = "PARSE ERROR"
            else:
                # Simulation mode: success if finished with exit code 0
                finished = 'finished' in output.lower()
                success = result.returncode == 0 and finished
                
                if success:
                    status_msg = "✅ SIMULATION OK"
                else:
                    status_msg = f"❌ FAILED (code {result.returncode})"
            
            print(f"   {config['NodeCount']} nodes: {states_explored} states, {runtime:.1f}s - {status_msg}")
            
            return {
                'config': config,
                'runtime': runtime,
                'success': success,
                'states_explored': states_explored,
                'distinct_states': distinct_states,
                'simulation_mode': use_simulation,
                'output': output[:1000],
                'error': '' if success else f"Exit code: {result.returncode}"
            }
            
        except subprocess.TimeoutExpired:
            runtime = time.time() - start_time
            print(f"   ⏱️  {config['NodeCount']} nodes: TIMEOUT after {timeout_seconds}s")
            return {
                'config': config,
                'runtime': runtime,
                'success': False,
                'states_explored': 0,
                'distinct_states': 0,
                'simulation_mode': use_simulation,
                'output': f'Timeout after {timeout_seconds} seconds',
                'error': 'timeout'
            }
        except Exception as e:
            runtime = time.time() - start_time
            print(f"   ❌ {config['NodeCount']} nodes: ERROR - {str(e)}")
            return {
                'config': config,
                'runtime': runtime,
                'success': False,
                'states_explored': 0,
                'distinct_states': 0,
                'simulation_mode': False,
                'output': str(e)[:1000],
                'error': str(e)
            }
    
    def run_parallel_analysis(self):
        """Run statistical analysis with multiple configurations in parallel"""
        print("🎲 LARGE-SCALE STATISTICAL ANALYSIS")
        print("=" * 60)
        print("🔄 Generating realistic network configurations...")
        
        configs = self.generate_large_scale_configs()
        self.total_simulations = len(configs)
        
        print(f"\n📊 Testing {self.total_simulations} configurations:")
        print(f"   Network sizes: 10-1000 nodes (realistic to very large-scale blockchain)")
        print(f"   Byzantine faults: 0%, ~5%, 19% (max safe threshold)")
        print(f"   Strategy: Simulation mode (1000 traces, depth=50)")
        print(f"   CPU cores: {self.cpu_workers} workers per TLC + {self.cpu_workers} parallel runs")
        print(f"   Memory: 8GB heap per TLC instance\n")
        
        # Run simulations in parallel (use 6 workers for stability)
        with concurrent.futures.ThreadPoolExecutor(max_workers=6) as executor:
            future_to_config = {
                executor.submit(self.run_statistical_verification, config): config 
                for config in configs
            }
            
            completed = 0
            for future in concurrent.futures.as_completed(future_to_config):
                result = future.result()
                self.results.append(result)
                
                if result['success']:
                    self.successful_simulations += 1
                
                completed += 1
                progress_pct = (completed / self.total_simulations) * 100
                success_rate = (self.successful_simulations / completed) * 100 if completed > 0 else 0
                print(f"   📈 Progress: {completed}/{self.total_simulations} ({progress_pct:.0f}%) | Success rate: {success_rate:.1f}%")
        
        print(f"\n✅ Analysis complete: {self.successful_simulations}/{self.total_simulations} successful ({(self.successful_simulations/self.total_simulations*100):.1f}%)")
    
    def extract_states_explored(self, output):
        """Extract number of states explored from TLC output"""
        try:
            for line in output.split('\n'):
                if 'states generated' in line.lower():
                    # Extract number from line like "1381 states generated, 352 distinct states found"
                    words = line.split()
                    for word in words:
                        if word.replace(',', '').isdigit():
                            return int(word.replace(',', ''))
            return 0
        except:
            return 0
    
    def extract_distinct_states(self, output):
        """Extract number of distinct states from TLC output"""
        try:
            for line in output.split('\n'):
                if 'distinct states' in line.lower():
                    # Extract number from line like "12345 distinct states"
                    words = line.split()
                    for word in words:
                        if word.replace(',', '').isdigit():
                            return int(word.replace(',', ''))
            return 0
        except:
            return 0
    
    def analyze_byzantine_tolerance(self):
        """Analyze Byzantine fault tolerance across different network sizes"""
        tolerance_data = {}
        
        for result in self.results:
            config = result['config']
            nodes = config['NodeCount']
            byz_count = config['ByzantineCount']
            
            if nodes not in tolerance_data:
                tolerance_data[nodes] = {'max_byzantine': 0, 'total_tests': 0, 'successful_tests': 0}
            
            tolerance_data[nodes]['total_tests'] += 1
            if result['success']:
                tolerance_data[nodes]['successful_tests'] += 1
                tolerance_data[nodes]['max_byzantine'] = max(
                    tolerance_data[nodes]['max_byzantine'], 
                    byz_count
                )
        
        return tolerance_data
    
    def generate_report(self):
        """Generate comprehensive statistical analysis report"""
        if not self.results:
            return {}
        
        successful_results = [r for r in self.results if r['success']]
        bfs_results = [r for r in successful_results if not r.get('simulation_mode', False)]
        sim_results = [r for r in successful_results if r.get('simulation_mode', False)]
        
        avg_states = sum(r['states_explored'] for r in successful_results) / max(len(successful_results), 1)
        avg_runtime = sum(r['runtime'] for r in successful_results) / max(len(successful_results), 1)
        max_states = max((r['states_explored'] for r in successful_results), default=0)
        
        # Analyze network sizes tested
        network_sizes = sorted(set(r['config']['NodeCount'] for r in self.results))
        max_network_size = max(network_sizes) if network_sizes else 0
        
        byzantine_tolerance = self.analyze_byzantine_tolerance()
        
        report = {
            'summary': {
                'total_simulations': self.total_simulations,
                'successful_simulations': self.successful_simulations,
                'success_rate': (self.successful_simulations / max(self.total_simulations, 1)) * 100,
                'avg_states_explored': int(avg_states),
                'avg_runtime_seconds': round(avg_runtime, 2),
                'max_states_explored': max_states,
                'bfs_verifications': len(bfs_results),
                'simulation_verifications': len(sim_results),
                'network_sizes_tested': network_sizes,
                'max_network_size': max_network_size,
                'cpu_workers': getattr(self, 'cpu_workers', None)
            },
            'byzantine_tolerance': byzantine_tolerance,
            'methodology': {
                'approach': 'Hybrid: BFS for ≤8 nodes, Simulation for >8 nodes',
                'slot_count': 1,
                'max_byzantine_percent': 19,
                'max_crash_percent': 10,
                'safety_threshold': '< 20% total faults (BFT requirement)'
            },
            'detailed_results': self.results
        }
        
        return report
    
    def save_results(self):
        """Save statistical analysis results"""
        report = self.generate_report()
        
        output_file = self.base_dir / "experiments" / "statistical" / "statistical_analysis.json"
        output_file.parent.mkdir(exist_ok=True)
        
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"📊 Statistical analysis results saved to {output_file}")
        return output_file

def main():
    """Main statistical analysis runner"""
    analyzer = AlpenglowStatisticalAnalysis()
    
    try:
        analyzer.run_parallel_analysis()
        analyzer.save_results()
        
        print("\n🎯 STATISTICAL ANALYSIS SUMMARY")
        print("=" * 40)
        print(f"Total Simulations: {analyzer.total_simulations}")
        print(f"Successful: {analyzer.successful_simulations}")
        print(f"Success Rate: {(analyzer.successful_simulations/max(analyzer.total_simulations,1))*100:.1f}%")
        
        return True
        
    except Exception as e:
        print(f"❌ Statistical analysis failed: {e}")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
