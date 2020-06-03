from setuptools import setup

setup(
    name='modelLang',
    version='0.1',
    packages=['modelLang',
              'modelLang/backends',
              'modelLang/parsers',
              'modelLang/structures',
              ],
    install_requires=[
        'coloredlogs==10.0',
        'ply==3.11',
        'pwntools==4.0.1',
        'pycparser==2.19',
        'z3==0.2.0',
        'z3-solver==4.8.7.0',
        'pefile==2019.4.18',
    ],
    maintainer='Dario Nisi',
    maintainer_email='dario.nisi@eurecom.fr'
)
