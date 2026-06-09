import asyncio
import aristotlelib

import logging

# Configure logging to see SDK messages
logging.basicConfig(
    level=logging.INFO,
    format="%(levelname)s - %(message)s"
)

async def main():
    # Prove theorems from a Lean file
    solution_path = await aristotlelib.Project.prove_from_file("Mathlib/Algebra/Group/Gromov/MatrixSubsum.lean")
    print(f"Solution saved to: {solution_path}")

asyncio.run(main())
